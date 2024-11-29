-- Simple progming language

inductive BINARY_OP where
  | Plus
  | Times
deriving Repr

inductive EXP where
  | Const     : Nat → EXP
  | BINARY_OP : BINARY_OP → EXP → EXP → EXP
deriving Repr

def binopDenote : BINARY_OP → Nat → Nat → Nat
  | .Plus  => Nat.add
  | .Times => Nat.mul

def expDenote : EXP → Nat
  | .Const n => n
  | .BINARY_OP b e1 e2 =>
    (binopDenote b) (expDenote e1) (expDenote e2)

-- testing...
#eval expDenote (EXP.Const 42)
#eval expDenote (EXP.BINARY_OP BINARY_OP.Plus (EXP.Const 2) (EXP.Const 3))
#eval expDenote (EXP.BINARY_OP BINARY_OP.Times (EXP.Const 7) (EXP.Const 6))

-- simple stack machine :)
inductive instr where
  | iConst     : Nat → instr
  | iBINARY_OP : BINARY_OP → instr
deriving Repr

def prog  := List instr
def stack := List Nat

def instrDenote : instr → stack → Option stack
  | instr.iConst n, s => some (n :: s)
  | instr.iBINARY_OP b, s =>
    match s with
    | arg1 :: arg2 :: s' => some ((binopDenote b) arg1 arg2 :: s')
    | _ => none

def progDenote (p : prog) (s : stack) : Option stack :=
  match p with
  | [] => some s
  | i :: p' =>
    match instrDenote i s with
    | none => none
    | some s' => progDenote p' s'

-- translation
def compile (e : EXP) : prog :=
  match e with
  | EXP.Const n           => [ instr.iConst n ]
  | EXP.BINARY_OP b e1 e2 =>
    (List.append (List.append (compile e2) (compile e1)) [ instr.iBINARY_OP b ])

-- testing compile
#eval compile (EXP.Const 42)
#eval compile (EXP.BINARY_OP BINARY_OP.Plus (EXP.Const 2) (EXP.Const 2))
#eval compile (EXP.BINARY_OP BINARY_OP.Times (EXP.Const 6) (EXP.Const 7))

-- testing progDenote
#eval progDenote (compile (EXP.Const 42)) []
#eval progDenote (compile (EXP.BINARY_OP BINARY_OP.Plus (EXP.Const 2) (EXP.Const 2))) []
#eval progDenote (compile (EXP.BINARY_OP BINARY_OP.Times (EXP.Const 6) (EXP.Const 7))) []


-- Let's prove that compile works corretly
theorem compile_correctly : ∀ e, progDenote (compile e) [] = some (expDenote e :: []) :=
  λ e => match e with
  | EXP.Const n => rfl
  | EXP.BINARY_OP b e1 e2 =>
    have IH1 : progDenote (compile e1) [] = some (expDenote e1 :: []) :=
      compile_correctly e1
    have IH2 : progDenote (compile e2) [] = some (expDenote e2 :: []) :=
      compile_correctly e2

show progDenote (compile (EXP.BINARY_OP b e1 e2)) [] =
  some (expDenote (EXP.BINARY_OP b e1 e2) :: [])
  from calc
    progDenote (compile (EXP.BINARY_OP b e1 e2)) [] =
    progDenote (List.append (List.append (compile e2) (compile e1)) [ instr.iBINARY_OP b ]) [] := by rfl

-- still thinking about it...
