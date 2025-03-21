-- This module serves as the root of the `FriFv` library.
-- Import modules here that should be built as part of the library.
import FriFv.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision

variable {F: Type} [Field F] [Finite F] [DecidableEq F]

noncomputable def fₑ (f : Polynomial F) : Polynomial F :=
  match f.degree with
  | none => 0
  | some n =>
    let X := Polynomial.X
    let minusX := -X
    (Polynomial.mul'.mul (Polynomial.C (2⁻¹ : F)) (f.comp X + f.comp minusX))

noncomputable def fₒ (f : Polynomial F) : Polynomial F :=
  match f.degree with
  | none => 0
  | some n =>
    let X := Polynomial.X
    let minusX := -X
    (Polynomial.mul'.mul (Polynomial.C (2⁻¹ : F)) (f.comp X - f.comp minusX)) /ₘ X

lemma fₑ_plus_x_mul_fₒ_eq_f {f : Polynomial F} : fₑ f + X * fₒ f = f := by
   unfold fₑ fₒ
   generalize h : f.degree = d
   rcases d with ⟨_ | d⟩ <;> simp
   symm
   rw [←Polynomial.degree_eq_bot]
   aesop
   sorry
