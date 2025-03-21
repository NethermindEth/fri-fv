-- This module serves as the root of the `FriFv` library.
-- Import modules here that should be built as part of the library.
import FriFv.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision

variable {F: Type} [Field F] [Finite F] [DecidableEq F]

noncomputable def fₑ (f : Polynomial F) (D : Fˣ -> Prop) : Polynomial F :=
  match f.degree with
  | none => 0
  | some n =>
    let X := Polynomial.X
    let minusX := -X
    (Polynomial.mul'.mul (Polynomial.C (2⁻¹ : F)) (f.comp X + f.comp minusX))

noncomputable def fₒ (f : Polynomial F) (D : Fˣ -> Prop) : Polynomial F :=
  match f.degree with
  | none => 0
  | some n =>
    let X := Polynomial.X
    let minusX := -X
    (Polynomial.mul'.mul (Polynomial.C (2⁻¹ : F)) (f.comp X - f.comp minusX)) /ₘ X
