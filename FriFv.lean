-- This module serves as the root of the `FriFv` library.
-- Import modules here that should be built as part of the library.
import FriFv.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision

variable {F: Type} [Field F] [Finite F] [DecidableEq F]

noncomputable def divide (f : Polynomial F) (D : Fˣ -> Prop) : Polynomial F :=
  match f.degree with
  | none => 0
  | some n =>
    let m := (n + 1) / 2
    let g := f.div (Polynomial.sub.sub (Polynomial.monomial (m : ℕ) 1) 1)
    let h := f.div (Polynomial.sub.sub (Polynomial.monomial (n - m) 1) 1)
    g + Polynomial.monomial (n - m) 1 * h
