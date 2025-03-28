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
  | some _ =>
    let X := Polynomial.X
    ((Polynomial.C (2⁻¹ : F)) * (f.comp X - f.comp (-X))) /ₘ (2 * X)

lemma fₑ_plus_x_mul_fₒ_eq_f {f : Polynomial F} : fₑ f + X * fₒ f = f := by
   unfold fₑ fₒ
   generalize h : f.degree = d
   rcases d with ⟨_ | d⟩ <;> simp
   symm
   rw [←Polynomial.degree_eq_bot]
   aesop
   sorry

variable (fₑ_x : Polynomial F → Polynomial F)
variable (fₒ_x : Polynomial F → Polynomial F)

lemma fₑ_is_even {f : Polynomial F} : fₑ f = (fₑ_x f).comp (Polynomial.X * Polynomial.X) := by
  sorry

lemma fₒ_is_even {f : Polynomial F} : fₒ f = (fₒ_x f).comp (Polynomial.X * Polynomial.X) := by
  sorry

noncomputable def foldα (f : Polynomial F) (α : F) : Polynomial F := (fₑ_x f) + (Polynomial.C α) * (fₒ_x f)

noncomputable def line_through_two_points (a₀ a₁ : F × F) : Polynomial F :=
  let x₀ := a₀.1
  let y₀ := a₀.2
  let x₁ := a₁.1
  let y₁ := a₁.2
  let m := (y₁ - y₀) / (x₁ - x₀)
  Polynomial.C m * Polynomial.X + Polynomial.C (y₀ - m * x₀)

noncomputable def consistency_check (x₀ : F) (s₀ s₁ : F) (α₀ α₁ β : F) : Bool :=
  let p := line_through_two_points (s₀, α₀) (s₁, α₁)
  let p_x₀ := p.eval x₀
  p_x₀ == β

lemma consistency_check_comp { f : Polynomial F }  {x₀ : F} {s₀ s₁ : F} {α₀ α₁ β : F} { h₁ : s₀ * s₀ = s₁ * s₁ }
  { h₂ : f.eval s₀ = α₀ } {h₃ : f.eval s₁ = α₁ } { h₄ : Polynomial.eval (s₀ * s₀) (foldα fₑ fₒ f x₀)= β } :
  consistency_check x₀ s₀ s₁ α₀ α₁ β = true := by
  sorry
