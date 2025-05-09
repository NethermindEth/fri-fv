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
    Polynomial.C (2⁻¹ : F) * (f.comp X + f.comp minusX)

noncomputable def fₒ (f : Polynomial F) : Polynomial F :=
    let X := Polynomial.X
    Polynomial.C (2⁻¹ : F) * (f.comp X - f.comp (-X)) /ₘ X

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

lemma fₑ_x_is_a_subst_of_fₑ {f : Polynomial F} : fₑ f = (fₑ_x f).comp (Polynomial.X * Polynomial.X) := by
  sorry

lemma fₒ_x_is_a_subst_of_fₑ {f : Polynomial F} : fₒ f = (fₒ_x f).comp (Polynomial.X * Polynomial.X) := by
  sorry

lemma fₑ_x_eval {f : Polynomial F} {x : F} : Polynomial.eval (x ^ 2) (fₑ_x f) = Polynomial.eval x (fₑ f) := by
  have hh : Polynomial.eval (x ^ 2) (fₑ_x f) = Polynomial.eval (x) ((fₑ_x f).comp (Polynomial.X * Polynomial.X)) := by
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X]
    ring_nf
  rw [hh, ←fₑ_x_is_a_subst_of_fₑ]

lemma fₒ_x_eval {f : Polynomial F} {x : F} : Polynomial.eval (x ^ 2) (fₒ_x f) = Polynomial.eval x (fₒ f) := by
  have hh : Polynomial.eval (x ^ 2) (fₒ_x f) = Polynomial.eval (x) ((fₒ_x f).comp (Polynomial.X * Polynomial.X)) := by
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X]
    ring_nf
  rw [hh, ←fₒ_x_is_a_subst_of_fₑ]

lemma fₑ_is_even {f : Polynomial F} {s₀ s₁ : F} {h : s₀ * s₀ = s₁ * s₁ } :
  Polynomial.eval s₀ (fₑ f) = Polynomial.eval s₁ (fₑ f) := by
    rw [←fₑ_x_eval, ←fₑ_x_eval]
    have hhh : s₀^2 = s₁ ^ 2 := by
        convert h <;> ring
    rw [hhh]


lemma fₒ_is_even' {f : Polynomial F} {s₀ s₁ : F} {h : s₀ * s₀ = s₁ * s₁ } :
  Polynomial.eval s₀ (fₒ f) = Polynomial.eval s₁ (fₒ f) := by
    rw [←fₒ_x_eval, ←fₒ_x_eval]
    have hhh : s₀^2 = s₁ ^ 2 := by
        convert h <;> ring
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

lemma the_glorious_lemma {x y : F} (z : F) (h : z ≠ 0) (h₁ : z * x = z * y ) : x = y := by
  have hh : x = 1 * x := by ring_nf
  rw [hh]
  have hh : y = 1 * y := by ring_nf
  rw [hh]
  have hh : 1 = z * z⁻¹ := by
    rw [Field.mul_inv_cancel]
    exact h
  conv =>
    lhs
    rw [hh, mul_comm z, mul_assoc, h₁]
    rfl
  conv =>
    rhs
    rw [hh, mul_comm z, mul_assoc,]
    rfl

lemma line_passing_through_the_poly { f : Polynomial F } {s₀ s₁ : F} {α₀ α₁ : F} { h₁ : s₀ * s₀ = s₁ * s₁ }
  { h₂ : f.eval s₀ = α₀ } {h₃ : f.eval s₁ = α₁ } {h₄ : s₀ ≠ s₁ }
   :
  line_through_two_points (s₀, α₀) (s₁, α₁) =
    Polynomial.C (Polynomial.eval (s₀^2) (fₑ_x f)) + Polynomial.X * (Polynomial.C (Polynomial.eval (s₀^2) (fₒ_x f))) := by
  unfold line_through_two_points
  simp only [map_sub, map_mul, Polynomial.X_mul_C]
  apply Polynomial.ext
  intro n
  rcases n with _ | n <;> simp
  · rw [←h₂, ←h₃, fₑ_x_eval]
    have hhh : Polynomial.eval s₀ f - (Polynomial.eval s₁ f - Polynomial.eval s₀ f) / (s₁ - s₀) * s₀ =
      ((s₁ - s₀ ) * Polynomial.eval s₀ f - s₀ * (Polynomial.eval s₁ f - Polynomial.eval s₀ f)) / (s₁ - s₀)
      := by
      have hhh : (s₁ - s₀) * (Polynomial.eval s₀ f - (Polynomial.eval s₁ f - Polynomial.eval s₀ f) / (s₁ - s₀) * s₀) = (s₁ - s₀) *
  ((s₁ - s₀) * Polynomial.eval s₀ f - s₀ * (Polynomial.eval s₁ f - Polynomial.eval s₀ f)) / (s₁ - s₀)  :=
    by {
        rw [div_eq_mul_inv, div_eq_mul_inv]
        conv =>
          rhs
          rw [mul_comm]
          rw [←mul_assoc, ←mul_comm (a := s₁ - s₀) (b := (s₁ - s₀)⁻¹) ]
          rw [Field.mul_inv_cancel _ (by {
          intro contr
          have hhh : s₁ = s₀ := by
            have hhh : s₀ = s₀ + 0 := by
              ring_nf
            rw [hhh, ←contr]
            ring_nf
          aesop
          })]
          rfl
        simp only [one_mul]
        conv =>
          lhs
          rw [mul_sub]
          congr
          rfl
          rw [mul_comm _ (s₁ - s₀)⁻¹]
          rw [←mul_assoc (s₁ - s₀), ←mul_assoc (s₁ - s₀)]
          rw [Field.mul_inv_cancel _ (by {
            intro contr
            have hhh : s₁ = s₀ := by
              have hhh : s₀ = s₀ + 0 := by
               ring_nf
              rw [hhh, ←contr]
              ring_nf
            aesop
          })]
        ring
      }
      apply (the_glorious_lemma (s₁ - s₀))
      · intro contr
        have hhh : s₁ = s₀ := by
          have hhh : s₀ = s₀ + 0 := by
            ring_nf
          rw [hhh, ←contr]
          ring_nf
        aesop
      · rw [hhh]
        ring_nf
    rw [hhh, div_eq_iff]
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
    rw [fₑ_is_even (s₀ := s₁) (s₁ := s₀) (h := by aesop)]
    ring_nf
    intro contr
    have hhh : s₁ = s₀ := by
      have hhh : s₀ = s₀ + 0 := by
        ring_nf
      rw [hhh, ←contr]
      ring_nf
    aesop
  · rcases n with _ | n <;> simp
    rw [←h₂, ←h₃, fₒ_x_eval]
    rw [div_eq_iff]
    conv =>
      lhs
      rw [←fₑ_plus_x_mul_fₒ_eq_f (f := f)]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    ring_nf
    rw [fₑ_is_even (s₀ := s₀) (s₁ := s₁) (h := h₁)]
    ring_nf
    rw [fₒ_is_even' (s₀ := s₁) (s₁ := s₀) (h := by aesop)]
    intro contr
    have hhh : s₁ = s₀ := by
      have hhh : s₀ = s₀ + 0 := by
        ring_nf
      rw [hhh, ←contr]
      ring_nf
    aesop

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
