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
      (List.mem_assoc x gamma) && (List.assoc x gamma = Var L), gamma

    | VarDeriv(x, T H) -> 
      expected_phrase = Exp(Var x) && (expected_type = T H) &&
      (List.mem_assoc x gamma) && (List.assoc x gamma = Var H), gamma

    | ConstDeriv(n) -> 
      (expected_phrase = (Exp(Int n))) && (expected_type = T L ), gamma

    | BinopDeriv(p, t, tree1, tree2) -> 
      begin 
        match p with
        | Exp(Binop(_, e1, e2)) -> 
          let verify_phrase = p = expected_phrase in 
          let verify_type = t = expected_type in
          let type_tree1, _ = aux tree1 (Exp e1) t gamma in
          let type_tree2, _ = aux tree2 (Exp e2) t gamma in
          verify_phrase && verify_type && type_tree1 && type_tree2, gamma
        |_ -> failwith"problem in the structure of the tree (binop)"
      end

    | SkipDeriv(t) -> t = Ncmd(H, 1), gamma

    | AssignDeriv(x, Exp exp, Ncmd(tau, 1), son_x, son_exp) when not (List.mem_assoc x gamma) -> 
      (*a definition of a new variable, inside a function *)
      let gamma' = (x, Var tau)::gamma in
      let verify_x_tree, _ = aux son_x (Exp(Var x)) (T tau) gamma' in 
      let verify_exp_tree, _ = aux son_exp (Exp exp) (T tau) gamma' in
      (expected_phrase = Command (Assign(x, exp))) && (expected_type = Ncmd(tau, 1)) &&
      verify_x_tree && verify_exp_tree, gamma'

    | AssignDeriv(x, Exp exp, Ncmd(tau, 1), son_x, son_exp) ->
      let verify_exp_tree, _ = aux son_exp (Exp exp) (T tau) gamma in 
      let verify_x_tree, _ = aux son_x (Exp(Var x)) (T tau) gamma in
      (expected_phrase = Command (Assign(x, exp))) && (expected_type = Ncmd(tau, 1)) &&
      (List.mem_assoc x gamma) && (List.assoc x gamma = Var tau) &&
      verify_exp_tree && verify_x_tree, gamma

    | IfDeriv(p, t, tree_exp, tree1, tree2) -> 
      begin
        match p with
        | Command(If(e, c1, c2)) -> 
          (
            match t with
            | Cmd(H, H) -> 
              let verify_phrase = p = expected_phrase in
              let verify_type = t = expected_type in
              let verify_exp, _ = aux tree_exp (Exp e) (T H) gamma in
              let verify_tree1, _ = aux tree1 (Command c1) t gamma in
              let verify_tree2, _ = aux tree2 (Command c2) t gamma in
              verify_phrase && verify_type && verify_exp && 
              verify_tree1 && verify_tree2, gamma

            | Cmd(tau1, tau2) -> 
              let verify_phrase = p = expected_phrase in
              let verify_type = t = expected_type in
              let verify_exp, _ = aux tree_exp (Exp e) (T L) gamma in
              let verify_tree1, _ = aux tree1 (Command c1) t gamma in
              let verify_tree2, _ = aux tree2 (Command c2) t gamma in
              verify_phrase && verify_type && verify_exp && 
              verify_tree1 && verify_tree2, gamma

            | Ncmd(tau, n) when n >= 1 ->
              let verify_phrase = p = expected_phrase in
              let verify_type = t = expected_type in
              let verify_exp, _ = aux tree_exp (Exp e) (T tau) gamma in
              let verify_tree1, _ = aux tree1 (Command c1) (Ncmd(tau, n - 1)) gamma in
              let verify_tree2, _ = aux tree2 (Command c2) (Ncmd(tau, n - 1)) gamma in
              verify_phrase && verify_type && verify_exp && 
              verify_tree1 && verify_tree2, gamma 

            |_ -> false, gamma

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
              let verify_exp, _ = aux tree_exp (Exp e) (T H) gamma in
              let verify_command, _ = aux tree_cmd (Command c) t gamma in
              verify_phrase && verify_type && verify_exp && verify_command, gamma

            | Cmd(tau1, tau2) -> 
              let verify_phrase = p = expected_phrase in
              let verify_type = t = expected_type in
              let verify_exp, _ = aux tree_exp (Exp e) (T L) gamma in
              let verify_command, _ = aux tree_cmd (Command c) t gamma in
              let comp = less_or_eq tau1 tau2 in
              verify_phrase && verify_type && verify_exp && 
              verify_command && comp, gamma

            |_ -> false, gamma

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
              let verify_c1, _ = aux tree1 (Command c1) t gamma in
              let verfiy_c2, _ = aux tree2 (Command c2) (Cmd(H, H)) gamma in
              verify_phrase && verify_type && verify_c1 && verfiy_c2, gamma

            | Cmd(tau1, tau2) -> 
              let verify_phrase = p = expected_phrase in
              let verify_type = t = expected_type in
              let verify_c1, _ = aux tree1 (Command c1) (Cmd(tau1, L)) gamma in
              let verfiy_c2, _ = aux tree2 (Command c2) t gamma in
              verify_phrase && verify_type && verify_c1 && verfiy_c2, gamma

            | _ -> false, gamma
          )

        |_ -> failwith"problem in the structure of the tree (Seq)"

      end

    | ReturnDeriv(e, t, tree1) -> 
      begin
        match t with
        | T tau -> 
          let verify_phrase = expected_phrase = Command(Return e) in
          let verify_type = expected_type = t in
          let verify_tree, _ = aux tree (Exp e) (T tau) gamma in
          verify_phrase && verify_type && verify_tree, gamma

        | _ -> false, gamma
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
            let verify_tree, gamma'' = aux tree1 (Command c1) (Ncmd(tau1, 1)) gamma' in 
            let verify_return = (List.mem_assoc y gamma'') && (List.assoc y gamma'' = Var tau2) in
            if verify_phrase && verify_type && verify_tree && verify_return then (functions_list := (f, c, t) :: !functions_list; true, gamma')
            else false, gamma'
            

          | _ -> false, gamma
          end

      | _ -> false, gamma
      )

    | FuncNonVoidCallDeriv(f, e, t, tree) -> 
      let verify_phrase = expected_phrase = Exp(FuncCall(f, e)) in
      let verify_type = expected_type = t in 
      begin
        match List.find (fun (g, _, _) -> g = f) !functions_list  with
        | (_, _, Func(tau1, tau2)) -> 
          begin
            match e, tau1 with
            | Var a, L -> let verify_tree, _ = aux tree (Exp e) (Var tau1) gamma in verify_phrase && verify_type && verify_tree, gamma
            | Int n , L-> let verify_tree, _ = aux tree (Exp e) (T tau1) gamma in verify_phrase && verify_type && verify_tree, gamma
            | _, _ -> false, gamma
          end

        | _ -> false, gamma  
      end
    
    | FuncVoidCallDeriv(f, x, c, t) -> 
      let verify_phrase = expected_phrase = Command(FuncDef(f, x, c)) in
      let verify_type = expected_type = t in
      begin
        match List.find (fun (g, _, _) -> g = f) !functions_list with
        | (_, _, Func(tau1, tau2)) -> 
          List.assoc x gamma = Var tau1 && t = T tau2 && verify_phrase && verify_type, gamma
        | _ -> false, gamma    
      end
    
    | SubDeriv(p, t1, t2, son1, subtype_tree) -> 
      let verify_phrase = p = expected_phrase in
      let verify_type = t1 = expected_type in
      let verify_son, _ = aux son1 p t2 gamma in
      let verify_subrules = check_sub_rules subtype_tree t2 t1 in
      verify_phrase && verify_type && verify_subrules && verify_son, gamma

    |_ -> false, gamma

    in let p, t = extract_phrase_and_type tree in
    fst (aux tree p t gamma)
