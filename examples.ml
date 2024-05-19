#use "type_checker.ml";;
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