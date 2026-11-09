/-- 自前で実装した自然数 -/
inductive MyNat where
  /-- ０ -/
  | zero
  /-- 後者関数 -/
  | succ (n : MyNat)

#check MyNat.zero

#check MyNat.succ

#check MyNat.succ .zero

/-- 自前で定義した 1 -/
def MyNat.one := MyNat.succ .zero

/-- 自前で定義した 2 -/
def MyNat.two := MyNat.succ .one

/-- MyNat 同士の足し算 -/
def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
--| .succ n => MyNat.succ (MyNat.add m n)
  | .succ n => succ (add m n)

set_option pp.fieldNotation.generalized false in

#check MyNat.add .one .one = .two

#reduce MyNat.add .one .one

#reduce MyNat.two

/-- 1 + 1 = 2 の MyNat における証明 -/
-- example : MyNat.add .one .one = .two := by
--   rfl
example : MyNat.one.add .one = .two := by
  rfl

example (n : MyNat) : MyNat.add n .zero = n := by
  rfl
