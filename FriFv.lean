-- This module serves as the root of the `FriFv` library.
-- Import modules here that should be built as part of the library.
import FriFv.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision

variable {F: Type} [Field F] [Finite F] [DecidableEq F]

noncomputable def fₑ (f : Polynomial F) : Polynomial F :=
    let X := Polynomial.X
    let minusX := -X
    ((Polynomial.C (2⁻¹ : F)) * (f.comp X + f.comp minusX))

noncomputable def fₒ (f : Polynomial F) : Polynomial F :=
    let X := Polynomial.X
    ((Polynomial.C (2⁻¹ : F)) * (f.comp X - f.comp (-X))) /ₘ (2 * X)

lemma fₑ_plus_x_mul_fₒ_eq_f {f : Polynomial F} : fₑ f + Polynomial.X * fₒ f = f := by
   unfold fₑ fₒ
   generalize h : f.degree = d
   rcases d with ⟨_ | d⟩ <;> simp
   · have h: f = 0 := by
      rw [← Polynomial.degree_eq_bot]
      aesop
     rw [h]
     simp
   · sorry

section

opaque fₑ_x : Polynomial F → Polynomial F := sorry
opaque fₒ_x : Polynomial F → Polynomial F := sorry

lemma fₑ_is_even {f : Polynomial F} : fₑ f = (fₑ_x f).comp (Polynomial.X * Polynomial.X) := by
  sorry

lemma fₒ_is_even {f : Polynomial F} : fₒ f = (fₒ_x f).comp (Polynomial.X * Polynomial.X) := by
  sorry

lemma fₑ_x_eval {f : Polynomial F} {x : F} : Polynomial.eval (x ^ 2) (fₑ_x f) = Polynomial.eval x (fₑ f) := by
  have hh : Polynomial.eval (x ^ 2) (fₑ_x f) = Polynomial.eval (x) ((fₑ_x f).comp (Polynomial.X * Polynomial.X)) := by
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X]
    ring_nf
  rw [hh, ←fₑ_is_even]

lemma fₒ_x_eval {f : Polynomial F} {x : F} : Polynomial.eval (x ^ 2) (fₒ_x f) = Polynomial.eval x (fₒ f) := by
  have hh : Polynomial.eval (x ^ 2) (fₒ_x f) = Polynomial.eval (x) ((fₒ_x f).comp (Polynomial.X * Polynomial.X)) := by
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X]
    ring_nf
  rw [hh, ←fₒ_is_even]

lemma fₑ_is_even' {f : Polynomial F} {s₀ s₁ : F} {h : s₀ * s₀ = s₁ * s₁ } : 
  Polynomial.eval s₀ (fₑ f) = Polynomial.eval s₁ (fₑ f) := by
    rw [←fₑ_x_eval, ←fₑ_x_eval]
    have hhh : s₀^2 = s₁ ^ 2 := by 
      sorry
    rw [hhh]


lemma fₒ_is_even' {f : Polynomial F} {s₀ s₁ : F} {h : s₀ * s₀ = s₁ * s₁ } : 
  Polynomial.eval s₀ (fₒ f) = Polynomial.eval s₁ (fₒ f) := by
    rw [←fₒ_x_eval, ←fₒ_x_eval]
    have hhh : s₀^2 = s₁ ^ 2 := by 
      sorry
    rw [hhh]

end

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

lemma line_passing_through_the_poly { f : Polynomial F } {s₀ s₁ : F} {α₀ α₁ : F} { h₁ : s₀ * s₀ = s₁ * s₁ }
  { h₂ : f.eval s₀ = α₀ } {h₃ : f.eval s₁ = α₁ } {h₄ : s₀ ≠ s₁ }
   :
  line_through_two_points (s₀, α₀) (s₁, α₁) =
    Polynomial.C (Polynomial.eval (s₀^2) (fₑ_x f)) + Polynomial.X * (Polynomial.C (Polynomial.eval (s₀^2) (fₒ_x f))) := by
  unfold line_through_two_points
  simp only [map_sub, map_mul, Polynomial.X_mul_C]
  apply Polynomial.ext
  intro n
  rcases n with ⟨_ | n⟩ <;> simp
  · rw [←h₂, ←h₃, fₑ_x_eval]
    have hhh : Polynomial.eval s₀ f - (Polynomial.eval s₁ f - Polynomial.eval s₀ f) / (s₁ - s₀) * s₀ =
      ((s₁ - s₀ ) * Polynomial.eval s₀ f - s₀ * (Polynomial.eval s₁ f - Polynomial.eval s₀ f)) / (s₁ - s₀) := by
        sorry
    rw [hhh]
    rw [div_eq_iff]
    ring_nf
    have hhh : s₁ * Polynomial.eval s₀ f - s₀ * Polynomial.eval s₁ f = 
      s₁ * Polynomial.eval s₀ (fₑ f + Polynomial.X * ( fₒ f )) - s₀ * Polynomial.eval s₁ ( fₑ f + Polynomial.X * ( fₒ f ) ) := by
      conv =>
        lhs
        rw [←fₑ_plus_x_mul_fₒ_eq_f (f := f)] 
    rw [hhh] 
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    ring_nf
    rw [fₒ_is_even' (s₀ := s₀) (s₁ := s₁) (h := h₁)]
    ring_nf  
    rw [fₑ_is_even' (s₀ := s₁) (s₁ := s₀) (h := by aesop)]
    ring_nf 
    sorry 
  · sorry



lemma consistency_check_comp { f : Polynomial F }  {x₀ : F} {y : F} {s₀ s₁ : F} {α₀ α₁ β : F} { h₁ : s₀ * s₀ = s₁ * s₁ }
  { h₂ : f.eval s₀ = α₀ } {h₃ : f.eval s₁ = α₁ } { h₄ : Polynomial.eval y (foldα f x₀)= β }
  { h₅ : s₀ * s₀ = y } {h₆ : s₀ ≠ s₁ } :
  consistency_check x₀ s₀ s₁ α₀ α₁ β = true := by
  unfold consistency_check
  simp
  rw [@line_passing_through_the_poly _ _ _ _ f s₀ s₁ α₀ α₁ h₁ h₂]
  simp only [Polynomial.X_mul_C, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X]
  rw [←h₄]
  unfold foldα
  rw [Polynomial.eval_add]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have hh : (s₀ ^ 2 = Polynomial.eval s₀ (Polynomial.X * Polynomial.X)) := by
    simp
    ring_nf
  rw [←h₅]
  ring_nf
  exact h₃
  exact h₆  
