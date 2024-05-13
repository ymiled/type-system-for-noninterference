type binop = 
  Plus | Minus | Mult | Div | Eq | Neq | Lt | Gt| Leq | Geq | And | Or

type exp = 
  | Int of int 
  | Var of string
  | Binop of binop * exp * exp 
  | FuncCall of string * exp

type command = 
  | Assign of string * exp 
  | Skip
  | If of exp * command * command 
  | While of exp * command 
  | Seq of command * command 
  | Return of exp
  | FuncDef of string * string * command
  
type phrase = 
  | Exp of exp
  | Command of command

type data_types = 
  | H 
  | L 

type phrase_type = 
  | T of data_types
  | Var of data_types
  | Func of data_types * data_types
  | Cmd of data_types * data_types
  | Ncmd of data_types * int

type var_type = string * phrase_type

let less_or_eq t1 t2 =
  match t1, t2 with
  | _, H -> true
  | t, t' when t = t' -> true
  | _, _ -> false


let functions_list = ref [("f", Skip, Func(L, L))]

type tree = 
  | Empty                                                           (* Red         *)
  | VarDeriv of string * phrase_type                                (* Orange      *)
  | ConstDeriv of int                                               (* Red         *)
  | BinopDeriv of phrase * phrase_type * tree * tree                (* Purple      *)
  | SkipDeriv of phrase_type                                        (* Red         *)
  | AssignDeriv of string * phrase * phrase_type * tree * tree      (* Light green *)
  | IfDeriv of phrase * phrase_type * tree * tree * tree            (* Pink        *)
  | WhileDeriv of phrase * phrase_type * tree * tree                (* Yellow      *)
  | SeqDeriv of phrase * phrase_type * tree * tree                  (* Dark green  *)
  | ReturnDeriv of exp * phrase_type * tree                              
  | FuncDefDeriv of string * string * command * phrase_type * tree  (* name, argument, command, type, tree for the command *)
  | FuncNonVoidCallDeriv of string * exp * phrase_type * tree            (* name, argument, type, tree for the expression *)
  | FuncVoidCallDeriv of string * string * command * phrase_type (* name, argument, command, type *)
  (* For the subtyping rules : *)
  | SubDeriv of phrase * phrase_type * phrase_type * tree * tree    (* Dark blue   *)
  | SubRules of phrase_type * phrase_type * tree * tree             (* Light blue  *)

exception Type_error

exception Phrase_error
    
let extract_phrase_and_type tree = 
  match tree with
  | VarDeriv(x, t) -> Exp(Var x), t 

  | ConstDeriv(n) -> Exp(Int n), T L

  | BinopDeriv(p, t, _, _) -> p, t

  | SkipDeriv(t) -> Command Skip, t

  | AssignDeriv(x, Exp e, t, _, _) -> Command(Assign(x, e)), t

  | IfDeriv(p, t, _, _, _) -> p, t 

  | WhileDeriv(p, t, _, _) -> p, t

  | SeqDeriv(p, t, _, _) -> p, t 

  | SubDeriv(p, t1, t2, _, _) -> p, t1

  | ReturnDeriv(e, t, _) -> Command(Return e), t

  | FuncDefDeriv(f, x, c, t, tree) -> Command(FuncDef(f, x, c)), t

  | FuncNonVoidCallDeriv(f, x, t, _) -> Exp(FuncCall(f, x)), t

  | FuncVoidCallDeriv(f, x, c, t) ->  Command c, t

  | _ -> raise Phrase_error


let rec check_sub_rules tree t1 t2 = 
  match tree with
  | SubRules(rho1, rho2, Empty, Empty) ->
    (t1 = rho1 && t2 = rho2) && 
    
    (* here we are in the case where we don't introduce another rho3 *)
    (* we only use base and cmd subtyping rules *)
    begin
      match rho1, rho2 with
      | T tau1, T tau2 -> less_or_eq tau1 tau2

      | Cmd(tau1, tau2), Cmd(tau1', tau2') -> 
        (less_or_eq tau1' tau1) && (less_or_eq tau2 tau2') 

      | Ncmd(tau, n), Ncmd(tau', n') when n = n' -> 
        less_or_eq tau' tau

      | Ncmd(tau, n), Cmd(tau', L) when tau = tau' -> true

      | Func(tau1, tau2), Ncmd(tau, n) -> true

      | Func(tau1, tau2), Func(tau1', tau2') -> 
        (less_or_eq tau1' tau1) && (less_or_eq tau2 tau2')  

      | _, _ when rho1 = rho2 -> true

      | _ -> false

    end 
  
  | SubRules(rho1, rho2, son1, son2) -> 
    (t1 = rho1 && t2 = rho2) &&
    (
      match son1, son2 with
      | SubRules(t1', t1'', _, _), SubRules(t2', t2'', _, _) ->
        (t1' = rho1) && (t1'' = t2') && (t2'' = rho2)  &&
        (check_sub_rules son1 rho1 t1'') && (check_sub_rules son2 t2' rho2) 

      |_ -> false

    )

  |_ -> failwith"problem in the structure of the tree (Subrules)"

let check_type tree gamma = 
  let rec aux tree expected_phrase expected_type gamma =
    match tree with
    | VarDeriv(x, T L) -> 
      expected_phrase = Exp(Var x) && (expected_type = T L) &&
      (List.mem_assoc x gamma) && (List.assoc x gamma = Var L)

    | VarDeriv(x, T H) -> 
      expected_phrase = Exp(Var x) && (expected_type = T H) &&
      (List.mem_assoc x gamma) && (List.assoc x gamma = Var H)

    | ConstDeriv(n) -> 
      (expected_phrase = (Exp(Int n))) && (expected_type = T L )

    | BinopDeriv(p, t, tree1, tree2) -> 
      begin 
        match p with
        | Exp(Binop(_, e1, e2)) -> 
          let verify_phrase = p = expected_phrase in 
          let verify_type = t = expected_type in
          let type_tree1 = aux tree1 (Exp e1) t gamma in
          let type_tree2 = aux tree2 (Exp e2) t gamma in
          verify_phrase && verify_type && type_tree1 && type_tree2
        |_ -> failwith"problem in the structure of the tree (binop)"
      end

    | SkipDeriv(t) -> t = Ncmd(H, 1)

    | AssignDeriv(x, Exp exp, Ncmd(tau, 1), son_x, son_exp) when not (List.mem_assoc x gamma) -> 
      (*a definition of a new variable, inside a function *)
      let gamma' = (x, Var tau)::gamma in
      (expected_phrase = Command (Assign(x, exp))) && (expected_type = Ncmd(tau, 1)) &&
      (aux son_x (Exp(Var x)) (T tau) gamma') && (aux son_exp (Exp exp) (T tau) gamma')

    | AssignDeriv(x, Exp exp, Ncmd(tau, 1), son_x, son_exp) ->
      (expected_phrase = Command (Assign(x, exp))) && (expected_type = Ncmd(tau, 1)) &&
      (List.mem_assoc x gamma) && (List.assoc x gamma = Var tau) &&
      (aux son_x (Exp(Var x)) (T tau) gamma) && (aux son_exp (Exp exp) (T tau) gamma)

    | IfDeriv(p, t, tree_exp, tree1, tree2) -> 
      begin
        match p with
        | Command(If(e, c1, c2)) -> 
          (
            match t with
            | Cmd(H, H) -> 
              let verify_phrase = p = expected_phrase in
              let verify_type = t = expected_type in
              let verify_exp = aux tree_exp (Exp e) (T H) gamma in
              let verify_tree1 = aux tree1 (Command c1) t gamma in
              let verify_tree2 = aux tree2 (Command c2) t gamma in
              verify_phrase && verify_type && verify_exp && 
              verify_tree1 && verify_tree2

            | Cmd(tau1, tau2) -> 
              let verify_phrase = p = expected_phrase in
              let verify_type = t = expected_type in
              let verify_exp = aux tree_exp (Exp e) (T L) gamma in
              let verify_tree1 = aux tree1 (Command c1) t gamma in
              let verify_tree2 = aux tree2 (Command c2) t gamma in
              verify_phrase && verify_type && verify_exp && 
              verify_tree1 && verify_tree2

            | Ncmd(tau, n) when n >= 1 ->
              let verify_phrase = p = expected_phrase in
              let verify_type = t = expected_type in
              let verify_exp = aux tree_exp (Exp e) (T tau) gamma in
              let verify_tree1 = aux tree1 (Command c1) (Ncmd(tau, n - 1)) gamma in
              let verify_tree2 = aux tree2 (Command c2) (Ncmd(tau, n - 1)) gamma in
              verify_phrase && verify_type && verify_exp && 
              verify_tree1 && verify_tree2 

            |_ -> false

          )

        |_ -> failwith"problem in the structure of the tree (if-else)"
      end

    | WhileDeriv(p, t, tree_exp, tree_cmd) ->
      begin
        match p with
        | Command (While(e, c)) -> 
          (
            match t with
            | Cmd(H, H) -> 
              let verify_phrase = p = expected_phrase in
              let verify_type = t = expected_type in
              let verify_exp = aux tree_exp (Exp e) (T H) gamma in
              let verify_command = aux tree_cmd (Command c) t gamma in
              verify_phrase && verify_type && verify_exp && verify_command

            | Cmd(tau1, tau2) -> 
              let verify_phrase = p = expected_phrase in
              let verify_type = t = expected_type in
              let verify_exp = aux tree_exp (Exp e) (T L) gamma in
              let verify_command = aux tree_cmd (Command c) t gamma in
              let comp = less_or_eq tau1 tau2 in
              verify_phrase && verify_type && verify_exp && 
              verify_command && comp

            |_ -> false

          )
        
        | _ -> failwith"problem in the structure of the tree (while)"

      end    

    | SeqDeriv(p, t, tree1, tree2) -> 
      begin
        match p with 
        | Command (Seq(c1, c2)) -> 
          (
            match t with
            | Cmd(tau, H) -> 
              let verify_phrase = p = expected_phrase in
              let verify_type = t = expected_type in
              let verify_c1 = aux tree1 (Command c1) t gamma in
              let verfiy_c2 = aux tree2 (Command c2) (Cmd(H, H)) gamma in
              verify_phrase && verify_type && verify_c1 && verfiy_c2

            | Cmd(tau1, tau2) -> 
              let verify_phrase = p = expected_phrase in
              let verify_type = t = expected_type in
              let verify_c1 = aux tree1 (Command c1) (Cmd(tau1, L)) gamma in
              let verfiy_c2 = aux tree2 (Command c2) t gamma in
              verify_phrase && verify_type && verify_c1 && verfiy_c2

            | _ -> false
          )

        |_ -> failwith"problem in the structure of the tree (Seq)"

      end

    | ReturnDeriv(e, t, tree1) -> 
      begin
        match t with
        | T tau -> 
          let verify_phrase = expected_phrase = Command(Return e) in
          let verify_type = expected_type = t in
          let verify_tree = aux tree (Exp e) (T tau) gamma in
          verify_phrase && verify_type && verify_tree

        | _ -> false
      end

    | FuncDefDeriv(f, x, c, t, tree1) ->
      (
      match t with
      | Func(tau1, tau2) ->
        let gamma' = (x, Var tau1)::gamma in
        begin
          match c with
          |Seq(c1, Return (Var y)) -> 
            let verify_phrase = expected_phrase = Command(FuncDef(f, x, c)) in
            let verify_type = expected_type = Func(tau1, tau2) in
            let verify_tree = aux tree1 (Command c1) (Ncmd(tau1, 1)) gamma' in 
            let verify_return = (List.mem_assoc y gamma') && (List.assoc y gamma' = Var tau2) in
            if verify_phrase && verify_type && verify_tree then (functions_list := (f, c, t) :: !functions_list; true)
            else false
            

          | _ -> false
          end

      | _ -> false
      )

    | FuncNonVoidCallDeriv(f, e, t, tree) -> 
      let verify_phrase = expected_phrase = Exp(FuncCall(f, e)) in
      let verify_type = expected_type = t in 
      begin
        match List.find (fun (g, _, _) -> g = f) !functions_list  with
        | (_, _, Func(tau1, tau2)) -> 
          begin
            match e, tau1 with
            | Var a, L -> aux tree (Exp e) (Var tau1) gamma
            | Int n , L-> aux tree (Exp e) (T tau1) gamma
            | _, _ -> false
          end

        | _ -> false  
      end
    
    | FuncVoidCallDeriv(f, x, c, t) -> 
      let verify_phrase = expected_phrase = Command(FuncDef(f, x, c)) in
      let verify_type = expected_type = t in
      begin
        match List.find (fun (g, _, _) -> g = f) !functions_list with
        | (_, _, Func(tau1, tau2)) -> 
          List.assoc x gamma = Var tau1 && t = T tau2 && verify_phrase && verify_type
        | _ -> false    
      end
    
    | SubDeriv(p, t1, t2, son1, subtype_tree) -> 
      let verify_phrase = p = expected_phrase in
      let verify_type = t1 = expected_type in
      let verify_son = aux son1 p t2 gamma in
      let verify_subrules = check_sub_rules subtype_tree t2 t1 in
      verify_phrase && verify_type && verify_subrules && verify_son

    |_ -> false

    in let p, t = extract_phrase_and_type tree in
    aux tree p t gamma


let ex1 = 
  SubDeriv(
    Command(Assign("y", (Int 5))),
    Cmd(L, L),
    Ncmd(L, 1),
    AssignDeriv("y", Exp(Int 5), Ncmd(L, 1), VarDeriv("y", T L) ,ConstDeriv(5)), 
    SubRules(Ncmd(L, 1), Cmd(L, L), Empty, Empty)
  )

let ex_inter = 
  SubDeriv(
    Command Skip, 
    Cmd(L, H), 
    Cmd(H, H), 
    SubDeriv(
      Command Skip, 
      Cmd(H, H), 
      Ncmd(H, 1), 
      SkipDeriv(Ncmd(H, 1)), 
      SubRules(
        Ncmd(H, 1), 
        Cmd(H, H), 
        SubRules(
          Ncmd(H, 1), 
          Cmd(H, L), 
          Empty, 
          Empty
        ), 
        SubRules(
          Cmd(H, L), 
          Cmd(H, H), 
          Empty, 
          Empty
        )
      )
    ), 
    SubRules(
      Cmd(H, H), 
      Cmd(L, H), 
      Empty, 
      Empty
    )
  )

let ex2 = 
  WhileDeriv(
    Command(While(
      Binop(Plus, Var "x", Int 1), 
      Skip
    )),
    Cmd(L, H),
    BinopDeriv(
      Exp(Binop(Plus, Var "x", Int 1)),
      T H,
      VarDeriv("x", T H),
      SubDeriv(
        Exp(Int 1),
        T H, 
        T L,
        ConstDeriv(1),
        SubRules(T L, T H, Empty, Empty)
      )
    ), 
    ex_inter
  )

let ex_final = 
  SeqDeriv(
    Command(
      Seq(
        Assign("y", Int 5), 
        While(
          Binop(Plus, Var "x", Int 1), 
          Skip
        )
      )
    ),
    Cmd(L, H),
    ex1, 
    ex2
  )

let tree1 = 
  BinopDeriv(
    Exp(Binop(Plus, Var "a", Int 1)),
    T L,
    VarDeriv("a", T L), 
    ConstDeriv(1)
  )

let tree2 = 
  SubDeriv(
    Command (Assign("b", Int 2)),
    Cmd(L, L),
    Ncmd(L, 1),
    AssignDeriv(
      "b", 
      Exp(Int 2), 
      Ncmd(L, 1), 
      VarDeriv("b", T L), 
      ConstDeriv(2)
    ), 
    SubRules(Ncmd(L, 1), Cmd(L, L), Empty, Empty)

  )

let tree3 = 
  SubDeriv(
    (Command Skip),
    Cmd(L, L),
    Ncmd(H, 1),
    SkipDeriv(Ncmd(H, 1)),
    SubRules(
      Ncmd(H, 1), 
      Cmd(L, L), 
      SubRules(Ncmd(H, 1), Cmd(H, L), Empty, Empty), 
      SubRules(Cmd(H, L), Cmd(L, L), Empty, Empty)
    )
    
  )


let ex = 
  IfDeriv(
    Command(
      If( Binop(Plus, Var "a", Int 1), Assign("b", Int 2), Skip)
      ),
    Cmd(L, L),
    tree1,
    tree2, 
    tree3

  )

let gamma = [("a", Var L); ("b", Var L)]

let functions_list = ref [];

functions_list := ("f", Seq (Assign("y", Binop(Plus, Var "x", Int 1)), Return (Var "y") ), Func(L, L)) :: !functions_list


(*functions_list := ("f", Seq (Assign("y", Binop(Plus, Var "x", Int 1)), Return (Var "y") ), Func(L, L)) :: !functions_list*)

let res = check_type ex gamma 

(*--------------------------------------------------------------------------------------------------------------------------------------*)

let example = "func f (int x) { y := x + 1; return y}; x := f(5)"

let assign_tree = 
  SubDeriv(
    Command (Assign("a", FuncCall("f", Int 5))),
    Cmd(L, L),   
    Ncmd(L, 1),  
    AssignDeriv(
      "a", 
      Exp (FuncCall("f", Int 5)), 
      Ncmd(L, 1), 
      VarDeriv("a", T L),
      FuncNonVoidCallDeriv("f", Int 5, T L, ConstDeriv(5))
    ), 
    SubRules(
      Ncmd(L, 1),
      Cmd(L, L),
      Empty, 
      Empty
    )
  )

let function_command_tree =
  AssignDeriv(
    "y", 
    Exp (Binop(Plus, Var "x", Int 1)),
    Ncmd(L, 1),
    VarDeriv("y", T L),
    BinopDeriv(
      Exp( Binop(Plus, Var "x", Int 1)),
      T L, 
      VarDeriv("x", T L), 
      ConstDeriv(1)
    )
  )


let func_tree = 
  SubDeriv(
    Command (FuncDef("f", "x", Seq( Assign("y", Binop(Plus, Var "x", Int 1)), (Return (Var "y")) ) )),
    Cmd(L, L), 
    Func(L, L),
    FuncDefDeriv(
      "f",
      "x",
      Seq( Assign("y", Binop(Plus, Var "x", Int 1)), (Return (Var "y")) ),
      Func(L, L),
      function_command_tree
    ),
    SubRules(
      Func(L, L), 
      Cmd(L, L), 
      SubRules(
        Func(L, L), 
        Ncmd(L, 1),
        Empty, 
        Empty
      ), 
      SubRules(
        Ncmd(L, 1), 
        Cmd(L, L),
        Empty, 
        Empty
      )
    )
  )


let example_proof_tree = 
  SeqDeriv(
    Command (
      Seq (
        FuncDef("f", "x", Seq( Assign("y", Binop(Plus, Var "x", Int 1)), (Return (Var "y")) ) ), 
        (Assign("a", FuncCall("f", Int 5)))
      )
    ), 
    Cmd(L, L), 
    func_tree, 
    assign_tree
  )


let test2 = check_type assign_tree [("a", Var L)]

let test3 = check_type func_tree [("a", Var L)]

let verification = check_type example_proof_tree [("a", Var L)]

