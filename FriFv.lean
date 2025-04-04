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
    Polynomial.C (2⁻¹ : F) * (f.comp X + f.comp (-X))

noncomputable def fₒ (f : Polynomial F) : Polynomial F :=
    let X := Polynomial.X
    Polynomial.C (2⁻¹ : F) * (f.comp X - f.comp (-X)) /ₘ X

def erase_odd' (s : Finset ℕ) (n : ℕ) : Finset ℕ := 
  match n with 
  | 0 => s
  | n + 1 => if n % 2 == 0 then erase_odd' (s.erase (n+1)) n else erase_odd' s n 

def erase_odd (s : Finset ℕ) : Finset ℕ :=
  let max := s.max 
  match max with
  | ⊥ => s 
  | some max => erase_odd' s max

lemma erase_odd'_is_subset_of_s {s : Finset ℕ} {d : ℕ} {n : ℕ} {hmem : n ∈ erase_odd' s d } : n ∈ s := by
  revert s
  induction d with 
  | zero => 
    intro s hmem 
    simp [erase_odd'] at hmem
    rcases n <;> aesop 
  | succ d ih => 
    intro s hmem 
    simp [erase_odd'] at hmem
    by_cases hd : d % 2 = 0
    · rw [hd] at hmem 
      simp at hmem 
      specialize (@ih (s.erase (d+1)) hmem)  
      aesop 
    · aesop 

lemma erase_odd_is_subset_of_s {s : Finset ℕ} {n : ℕ} {hmem : n ∈ erase_odd s } : n ∈ s := by
  simp [erase_odd] at hmem  
  generalize h : s.max = max 
  rcases max 
  · aesop 
  · apply erase_odd'_is_subset_of_s
    aesop 

lemma erase_odd'_odd_mem {s : Finset ℕ} {n : ℕ} {h : Odd n} {d : ℕ} {h_le : n ≤ d} :
    n ∉ erase_odd' s d := by
  revert n s 
  induction d with 
  | zero => 
    simp [erase_odd']
    aesop 
  | succ d ih => 
    simp [erase_odd']
    intros s n h h_le  
    by_cases hd : d % 2 = 0
    · simp [hd]
      rcases h_le with h_le | h_le 
      · intro contr 
        have h :=erase_odd'_is_subset_of_s (s := s.erase (d+1)) (hmem := contr)
        aesop 
      · intro contr 
        have hh :=erase_odd'_is_subset_of_s (s := s.erase (d+1)) (hmem := contr)
        aesop 
    · rcases h_le with h_le | h_le 
      · unfold Odd at h 
        rcases h with ⟨k, h⟩
        have h : d = 2 * k := by aesop 
        aesop 
      · aesop 

lemma erase_odd'_bound {s : Finset ℕ} {n : ℕ} {d : ℕ} {h_gt : n > d} {hmem : n ∈ s } : 
    n ∈ erase_odd' s d := by 
    revert s n 
    induction d with 
    | zero => 
      simp [erase_odd']
    | succ d ih =>
      intro s n h_gt hmem 
      simp [erase_odd']
      by_cases hd : d % 2 = 0 
      · rw [hd] 
        simp 
        apply ih <;> try omega 
        aesop 
      · aesop 
        apply ih <;> try omega 
        tauto 

lemma erase_odd'_even_mem {s : Finset ℕ} {n : ℕ} {h : Even n} {d : ℕ} {h_le : n ≤ d} {h_mem : n ∈ s } : n ∈ erase_odd' s d  
      := by
  revert n s 
  induction d with 
  | zero => 
    simp [erase_odd']
  | succ d ih => 
    simp [erase_odd']
    intros s n h h_le h_mem
    by_cases hd : d % 2 = 0
    · simp [hd]
      rcases h_le with h_le | h_le 
      · unfold Even at h 
        rcases h with ⟨k, h⟩ 
        have hhh : (d+1) % 2 = 0 := by 
          have hhh : k + k = 2 * k := by omega 
          aesop 
        have hhh : d % 2 + 1 = 0 := by omega 
        omega 
      · apply ih <;> try tauto 
        simp [erase_odd']
        aesop 
    · rcases h_le with h_le | h_le 
      · aesop 
        apply erase_odd'_bound <;> try omega 
        tauto 
      · aesop  

lemma erase_odd_odd_mem {s : Finset ℕ} {n : ℕ} {h : Odd n} : n ∉ (erase_odd s) := by
  generalize hmax : s.max = max 
  rcases max with _ | d <;> simp [erase_odd]
  · have hbot : none = (⊥ : WithBot ℕ) := by rfl
    rw [hbot, Finset.max_eq_bot] at hmax
    simp [hmax]
  · simp [hmax]
    by_cases hn : n ≤ d 
    · apply erase_odd'_odd_mem <;> try tauto 
    · intro contr 
      have hhh := erase_odd'_is_subset_of_s (s := s) (d := d) (n := n) (hmem := contr)
      aesop 
      have hhhh := Finset.le_max hhh 
      rw [hmax] at hhhh 
      have hhhh : n ≤ d := by
        rw [WithBot.le_def] at hhhh 
        specialize (hhhh n) 
        simp at hhhh 
        aesop 
        have hw : some d = some w := by 
          rw [left] 
          rfl 
        rw [Option.some_inj] at hw 
        omega 
      omega 

lemma erase_odd_even_mem {s : Finset ℕ} {n : ℕ} {he : Even n} : n ∈ (erase_odd s) ↔ n ∈ s := by 
  apply Iff.intro <;> intro h 
  · apply erase_odd_is_subset_of_s 
    tauto 
  · unfold erase_odd 
    generalize hmax : s.max = max 
    rcases max with _ | max 
    · simp [h]
    · simp 
      by_cases hle : n ≤ max 
      · apply erase_odd'_even_mem <;> try tauto 
      · aesop 
        have hhhh := Finset.le_max h
        have hhhh : n ≤ max := by
          rw [WithBot.le_def] at hhhh 
          specialize (hhhh n) 
          simp at hhhh 
          aesop   
          have hw : some max = some w := by 
            rw [left] 
            rfl 
          rw [Option.some_inj] at hw 
          omega 
        omega 

noncomputable def fₑ' (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, f, pr⟩⟩ => ⟨⟨erase_odd supp, fun n => if n % 2 == 0 then f n else 0, by {
    
  }⟩⟩  

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
