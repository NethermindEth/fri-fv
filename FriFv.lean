-- This module serves as the root of the `FriFv` library.
-- Import modules here that should be built as part of the library.
import FriFv.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert

variable {F: Type} [Field F] [Finite F] [DecidableEq F]

noncomputable def fₑ (f : Polynomial F) : Polynomial F :=
    let X := Polynomial.X
    Polynomial.C (2⁻¹ : F) * (f + f.comp (-X))

noncomputable def fₒ (f : Polynomial F) : Polynomial F :=
    let X := Polynomial.X
    Polynomial.C (2⁻¹ : F) * (f - f.comp (-X)) /ₘ X

def erase_odd (s : Finset ℕ) : Finset ℕ := s.filter Even
def erase_even (s : Finset ℕ) : Finset ℕ := s.filter Odd

noncomputable def fₑ' (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, f, pr⟩⟩ => ⟨⟨erase_odd supp, fun n => if Even n then f n else 0, by {unfold erase_odd; aesop}⟩⟩

noncomputable def x_times_fₒ' (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, f, pr⟩⟩ => ⟨⟨erase_even supp, fun n => if Odd n then f n else 0, by {unfold erase_even; aesop}⟩⟩


noncomputable def fₒ' (f : Polynomial F) : Polynomial F :=
    match f with
  | ⟨⟨supp, f, pr⟩⟩ =>
  ⟨
    (erase_even supp).filterMap
      (λ n ↦
        match n with
        | 0 => .none
        | n + 1 => .some n
      )
      (by aesop),
    fun n => if Even n then f (n + 1) else 0,
    by {
      intro a
      by_cases h : Even a <;> simp [h]
      · unfold erase_even
        simp [(pr (a + 1)).symm]
        apply Iff.intro
        · rintro ⟨a', h⟩; aesop
        · intros h
          exists (a + 1)
          aesop
      · unfold erase_even
        intros x h'
        by_cases h'' : x = a.succ
        · rw [Finset.mem_filter, h''] at h'
          exfalso
          apply h
          rw [Nat.odd_add_one] at h'
          aesop
        · aesop
    }
  ⟩

lemma x_times_fₒ'_eq_x_times_fₒ' {f : Polynomial F} :
    Polynomial.X * (fₒ' f) = x_times_fₒ' f := by
  apply Polynomial.ext
  intro n
  unfold fₒ' x_times_fₒ'
  simp
  rcases f with ⟨⟨supp, g, h⟩⟩
  rcases n with _ | n
  · simp
  · simp
    by_cases hpar : Even n
    · simp [hpar]
    · simp [Nat.odd_add_one, hpar]

lemma coeffs_of_fₑ' {f : Polynomial F} {n : ℕ}:
    (fₑ' f).coeff n = if Even n then f.coeff n else 0 := by
  unfold fₑ'
  rcases f with ⟨⟨supp, g, h⟩⟩
  simp

lemma coeffs_of_comp_minus_x {f : Polynomial F} {n : ℕ} :
    (f.comp (-Polynomial.X)).coeff n = if Even n then f.coeff n else -f.coeff n := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.coeff_sum, Polynomial.sum_def]
  have coeff_lem {n n' : ℕ} : ((- Polynomial.X) ^ n').coeff n = if n = n' then (-1)^n else 0 := by sorry
  simp only [Polynomial.coeff_C_mul]


  by_cases h : Even n <;> simp [h]
  · sorry
  · sorry

lemma fₑ_eq_fₑ' {f : Polynomial F} {hchar : (2 : F) ≠ 0} : fₑ f = fₑ' f := by
  apply Polynomial.ext
  intro n
  rw [coeffs_of_fₑ']
  by_cases hpar : Even n
  · simp [hpar]
    unfold fₑ
    simp
    conv =>
      lhs
      rw [mul_add]
      rfl
    rw [coeffs_of_comp_minus_x]
    simp [hpar]
    ring_nf
    have hhh : (2 : F) * 2⁻¹ = 1 := by
      rw [Field.mul_inv_cancel]
      exact hchar
    rw [mul_comm, ←mul_assoc, hhh]
    simp
  · simp [hpar]
    unfold fₑ
    simp
    rw [coeffs_of_comp_minus_x]
    simp [hpar]


lemma fₒ_eq_fₒ'_aux {f : Polynomial F} {hchar : (2 : F) ≠ 0 } : (Polynomial.C (2⁻¹ : F)) * (f - f.comp (-Polynomial.X)) = x_times_fₒ' f := by
  apply Polynomial.ext
  intro n
  simp
  rw [coeffs_of_comp_minus_x]
  unfold x_times_fₒ'
  rcases f with ⟨⟨supp, g, hhh⟩⟩
  simp
  by_cases hpar : Even n
  · simp [hpar]
    rw [←Nat.not_odd_iff_even] at hpar
    simp [hpar]
  · simp [hpar]
    simp only [← Nat.not_odd_iff_even, Decidable.not_not] at hpar
    simp [hpar]
    ring_nf
    rw [mul_comm, ←mul_assoc]
    have hhhhh : (2 : F) * 2⁻¹ = 1 := by
      apply Field.mul_inv_cancel
      exact hchar
    rw [hhhhh]
    ring

lemma fₒ_eq_fₒ'_aux' {f : Polynomial F} {hchar : (2 : F) ≠ 0 } : (f - f.comp (-Polynomial.X)) = (Polynomial.C 2) * x_times_fₒ' f := by
  apply Polynomial.ext
  intro n
  simp
  rw [←fₒ_eq_fₒ'_aux]
  aesop
  exact hchar

lemma fₒ_eq_fₒ' {f : Polynomial F} {hchar : (2: F) ≠ 0 } : fₒ' f = fₒ f := by
  unfold fₒ
  simp
  rw [fₒ_eq_fₒ'_aux' (hchar := hchar) ]
  rw [←x_times_fₒ'_eq_x_times_fₒ']
  rw [←mul_assoc]
  rw [←Polynomial.C_mul]
  have hhh : 2⁻¹ * (2 : F) = 1 := by
    rw [mul_comm]
    apply Field.mul_inv_cancel
    tauto
  rw [hhh]
  simp
  rw [Polynomial.mul_divByMonic_cancel_left]
  aesop

lemma fₑ_plus_x_mul_fₒ_eq_f {f : Polynomial F} {hchar : (2 : F) ≠ 0} : fₑ f + Polynomial.X * fₒ f = f := by
  rw [←fₒ_eq_fₒ' (hchar := hchar)]
  rw [fₑ_eq_fₑ' (hchar := hchar)]
  apply Polynomial.ext
  intro n
  unfold fₒ' fₑ'
  rcases f with ⟨⟨supp, g, hhhh⟩⟩
  simp
  by_cases hpar : Even n
  · simp [hpar]
    rcases n with _ | n
    · simp
    · simp
      intros h
      rw [even_iff_exists_two_mul] at h hpar
      omega
  · simp [hpar]
    rcases n with _ | n
    · simp at hpar
    · simp
      intros h
      have bla := Odd.add_one h
      aesop

section

def divide_by_2' (s : Finset ℕ) (acc : Finset ℕ) (n : ℕ) : Finset ℕ :=
  match n with
  | 0 => if 0 ∈ s then insert 0 acc else acc
  | n + 1 => if 2 * (n+1) ∈ s then divide_by_2' s (insert (n+1) acc) n else divide_by_2' s acc n

def divide_by_2 (s : Finset ℕ) : Finset ℕ :=
  match s.max with
  | ⊥ => s
  | some max => divide_by_2' s Finset.empty max

lemma divide_by_2'_contains_accum {s : Finset ℕ} {acc : Finset ℕ} {n : ℕ} {d : ℕ } {hmem : d ∈ acc} :
    d ∈ divide_by_2' s acc n := by
  revert s acc d
  induction n with
  | zero =>
    intros s acc d hmem
    unfold divide_by_2'
    aesop
  | succ n ih =>
    intros s acc d hmem
    unfold divide_by_2'
    by_cases hif : 2 * (n + 1) ∈ s
    · simp [hif]
      apply ih
      aesop
    · simp [hif]
      apply ih
      exact hmem

lemma divide_by_2'_mem {s : Finset ℕ} {acc : Finset ℕ} {n : ℕ} {d : ℕ } { hle : d ≤ n } : 2 * d ∈ s → d ∈ divide_by_2' s acc n := by
  revert s acc d
  induction n with
  | zero =>
    intros s acc d hle h
    unfold divide_by_2'
    have hhh : d = 0 := by omega
    aesop
  | succ n ih =>
    intros s acc d hle h
    unfold divide_by_2'
    by_cases hmem : 2 * (n + 1) ∈ s
    · simp [hmem]
      rcases hle with hle | hle
      · apply divide_by_2'_contains_accum
        aesop
      · apply ih <;> try tauto
    · simp [hmem]
      rcases hle with hle | hle <;> try tauto

lemma divide_by_2'_mem_bound {s : Finset ℕ} {acc : Finset ℕ} {n : ℕ} {d : ℕ } {hnmem : d ∉ acc}:
    d ∈ divide_by_2' s acc n → d ≤ n := by
  revert s acc d
  induction n with
  | zero =>
    intros s acc d hnmem
    unfold divide_by_2'
    aesop
  | succ n ih =>
    intros s acc d hnmem h
    by_cases hmem : 2 * (n + 1) ∈ s
    · unfold divide_by_2' at h
      simp [hmem] at h
      by_cases hd : d = n + 1 <;> try omega
      apply Nat.le_succ_of_le
      apply (ih (acc := (insert (n + 1) acc)))
      exact h
      aesop
    · unfold divide_by_2' at h
      simp [hmem] at h
      by_cases hd : d = n + 1 <;> try omega
      apply Nat.le_succ_of_le
      apply (ih (acc := acc)) <;> try tauto


lemma divide_by_2'_mem_char {s : Finset ℕ} {acc : Finset ℕ} {n : ℕ} {d : ℕ } :
    d ∈ divide_by_2' s acc n → d ∈ acc ∨ 2 * d ∈ s := by
  intros h
  by_cases hmem : d ∈ acc <;> try tauto
  right
  have hhh : d ≤ n := by apply divide_by_2'_mem_bound (s := s) (acc := acc) (n := n) (hnmem := hmem) <;> try tauto
  revert s acc d
  induction n with
  | zero =>
    intros s acc d h hnin
    unfold divide_by_2' at h
    aesop
  | succ n ih =>
    intros s acc d h hnin hle
    unfold divide_by_2' at h
    by_cases hif : 2*(n+1) ∈ s
    · simp [hif] at h
      rcases hle with hle | hle <;> try tauto
      apply ih
      exact h
      aesop
      exact hle
    · simp [hif] at h
      rcases hle with hle | hle <;> try tauto
      have hhh := divide_by_2'_mem_bound (hnmem := hnin) h
      omega

lemma divide_by_2_mem {s : Finset ℕ} {d : ℕ} :
  d ∈ divide_by_2 s ↔ 2 * d ∈ s := by
  unfold divide_by_2
  generalize hmax : s.max = m
  rcases m with m | m
  · simp
    have hhh : s.max = ⊥ := by exact hmax
    rw [Finset.max_eq_bot] at hhh
    aesop
  · simp
    apply Iff.intro
    · intros h
      have h := divide_by_2'_mem_char h
      tauto
    · intros h
      have h := divide_by_2'_mem (s := s) (n := m) (acc := Finset.empty) h (hle := by {
        have hh : 2 * d ≤ m := by
          have hh := Finset.le_max h
          rw [hmax] at hh
          specialize (hh (2*d))
          simp at hh
          rcases hh with ⟨k, hh⟩
          have hhh : k = m := by
            apply Option.some_injective
            rw [hh.1]
            rfl
          omega
        omega
      })
      exact h

noncomputable def evenize (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, g, h⟩⟩ => ⟨⟨divide_by_2 supp, fun n => g (2 * n), by {
    intros a
    rw [divide_by_2_mem, h]
  }⟩⟩

def mul_by_2' (s : Finset ℕ) (acc : Finset ℕ) (n : ℕ) : Finset ℕ :=
  match n with
  | 0 => if 0 ∈ s then insert 0 acc else acc
  | n + 1 => if (n + 1) ∈ s then mul_by_2' s (insert (2 * (n + 1)) acc) n else mul_by_2' s acc n

def mul_by_2 (s : Finset ℕ) : Finset ℕ :=
  match s.max with
  | ⊥ => s
  | some m => mul_by_2' s Finset.empty m

lemma mul_by_2'_contains_accum {s : Finset ℕ} {acc : Finset ℕ} {n : ℕ} {d : ℕ} :
    d ∈ acc → d ∈ mul_by_2' s acc n := by
  revert s acc d
  induction n with
  | zero =>
    intros s acc d h
    unfold mul_by_2'
    aesop
  | succ n ih =>
    intros s acc d h
    unfold mul_by_2'
    by_cases hif : n + 1 ∈ s
    · simp [hif]
      apply ih
      aesop
    · simp [hif]
      apply ih
      exact h

lemma mul_by_2'_acc_mem {s : Finset ℕ} {acc : Finset ℕ} {n : ℕ} {d : ℕ} {hnin : d ∉ s}:
    2 * d ∈ mul_by_2' s acc n → 2 * d ∈ acc := by
  revert s acc d
  induction n with
  | zero =>
    intros s acc d hnin h
    unfold mul_by_2' at h
    aesop
  | succ n ih =>
    intros s acc d hnin h
    unfold mul_by_2' at h
    by_cases hif : n+1 ∈ s
    · simp [hif] at h
      specialize (ih (d := d) (s := s) (acc :=(insert (2 * (n + 1)) acc)) (hnin := by {
        exact hnin
      }) h)
      aesop
    · simp [hif] at h
      apply ih
      exact hnin
      exact h

lemma mul_by_2'_mem {s : Finset ℕ} {acc : Finset ℕ} {n : ℕ} {d : ℕ} {hle : d ≤ n} :
    2 * d ∈ mul_by_2' s acc n ↔ d ∈ s ∨ 2 * d ∈ acc := by
  revert s acc d hle
  induction n with
  | zero =>
    intros s acc n d
    unfold mul_by_2'
    aesop
  | succ n ih =>
    intros s acc d hle
    unfold mul_by_2'
    by_cases hif : n + 1 ∈ s
    · simp [hif]
      rcases hle with hle | hle
      · aesop
        apply mul_by_2'_contains_accum
        aesop
      · aesop
    · simp [hif]
      rcases hle with hle | hle
      · aesop
        apply mul_by_2'_acc_mem
        exact hif
        apply a
        apply mul_by_2'_contains_accum
        exact a
      · aesop

lemma mul_by_2'_bound {s : Finset ℕ} {acc : Finset ℕ} {n : ℕ} {d : ℕ} {hnin : d > n}:
    2 * d ∈ mul_by_2' s acc n → 2 * d ∈ acc := by
  revert s acc d
  induction n with
  | zero =>
    intros s acc d hnin
    unfold mul_by_2'
    aesop
  | succ n ih =>
    intros s acc d hnin h
    unfold mul_by_2' at h
    by_cases hmem : n+1 ∈ s
    · simp [hmem] at h
      specialize (ih (acc := (insert (2 * (n + 1)) acc)) (s := s) (d := d) h)
      omega
      aesop
    · simp [hmem] at h
      apply ih
      omega
      exact h

lemma mul_by_2'_abs_bound {s : Finset ℕ} {acc : Finset ℕ} {n : ℕ} {d : ℕ} {hnin : d > 2 * n}:
    d ∈ mul_by_2' s acc n → d ∈ acc := by
  revert s acc d
  induction n with
  | zero =>
    intros s acc d hnin
    unfold mul_by_2'
    aesop
  | succ n ih =>
    intros s acc d hnin h
    unfold mul_by_2' at h
    by_cases hmem : n+1 ∈ s
    · simp [hmem] at h
      specialize (ih (acc := (insert (2 * (n + 1)) acc)) (s := s) (d := d) h)
      omega
      aesop
    · simp [hmem] at h
      apply ih
      omega
      exact h

lemma mul_by_2'_not_mem_odd {s : Finset ℕ} {acc : Finset ℕ} {n : ℕ} {d : ℕ} :
    (2 * d + 1) ∈ mul_by_2' s acc n → 2 * d + 1 ∈ acc := by
  revert s acc d
  induction n with
  | zero =>
    intro s acc d h
    unfold mul_by_2' at h
    aesop
  | succ n ih =>
    intros s acc d h
    by_cases hle : d ≤ (n + 1)
    · rcases hle with hle | hle
      · unfold mul_by_2' at h
        by_cases hif : (n + 1 ∈ s)
        · simp [hif] at h
          specialize (ih h)
          aesop
        · simp [hif] at h
          specialize (ih h)
          tauto
      · unfold mul_by_2' at h
        by_cases hif : (n + 1 ∈ s)
        ·
          simp [hif] at h
          specialize (ih h)
          aesop
          omega
        · simp [hif] at h
          specialize (ih h)
          tauto
    · unfold mul_by_2' at h
      by_cases hmem : n+1 ∈ s
      · simp [hmem] at h
        have hhh := mul_by_2'_abs_bound (acc :=(insert (2 * (n + 1)) acc)) (d := 2*d + 1) (n := n) (s := s) (hnin := by {
          omega
        }) h
        rw [Finset.mem_insert] at hhh
        rcases hhh with hhh | hhh <;> try tauto
        omega
      · simp [hmem] at h
        apply ih
        exact h

lemma mul_by_2_mem {s : Finset ℕ} {d : ℕ} :
    2 * d ∈ mul_by_2 s ↔ d ∈ s := by
  generalize hmax : s.max = m
  unfold mul_by_2
  rcases m with _ | m
  · have hhh : s.max = ⊥ := by exact hmax
    rw [Finset.max_eq_bot] at hhh
    aesop
  · simp [hmax]
    by_cases hle : d ≤ m
    · rw [mul_by_2'_mem] <;> try tauto
    · have hh : d ∉ s := by
        intro contr
        have hh := Finset.le_max contr
        specialize (hh d)
        simp at hh
        rcases hh with ⟨k, hh⟩
        have hhh : k = m := by
            apply Option.some_injective
            rw [hmax] at hh
            rw [hh.1]
            rfl
        omega
      aesop
      have hhh := mul_by_2'_bound a (hnin := by tauto)
      tauto

lemma mul_by_2_not_mem_odd {s : Finset ℕ} {d : ℕ} :
    (2 * d + 1) ∉ mul_by_2 s := by
  intro contr
  unfold mul_by_2 at contr
  generalize hmax : s.max = m
  rcases m with _ | m
  · simp [hmax] at contr
    have hhh : s.max = ⊥ := by exact hmax
    rw [Finset.max_eq_bot] at hhh
    aesop
  · simp [hmax] at contr
    have hhh := mul_by_2'_not_mem_odd contr
    tauto

noncomputable def deevenize (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, g, h⟩⟩ => ⟨⟨mul_by_2 supp, fun n => if n % 2 = 0 then g (n / 2) else 0, by {
    intro a
    by_cases hpar : a % 2 = 0
    · simp [hpar]
      rw [←Nat.even_iff] at hpar
      rcases hpar with ⟨k, hpar⟩
      rw [hpar]
      have hh : k + k = 2 * k := by omega
      rw [hh]
      rw [mul_by_2_mem]
      aesop
    · simp [hpar]
      have hpar : Odd a := by
        rw [Nat.odd_iff]
        omega
      unfold Odd at hpar
      rcases hpar with ⟨k, hpar⟩
      rw [hpar]
      apply mul_by_2_not_mem_odd
  }⟩⟩

lemma comp_x_sqrt_eq_deevenized {f : Polynomial F} :
    deevenize f = f.comp (Polynomial.X * Polynomial.X) := by
  apply Polynomial.ext
  intro n
  unfold deevenize
  rcases f with ⟨⟨supp, g, h⟩⟩
  simp
  sorry

noncomputable def fₑ_x (f : Polynomial F) : Polynomial F := evenize (fₑ f)
noncomputable def fₒ_x (f : Polynomial F) : Polynomial F := evenize (fₒ f)

lemma fₑ_x_is_a_subst_of_fₑ {f : Polynomial F} {hchar : (2 : F) ≠ 0} : fₑ f = (fₑ_x f).comp (Polynomial.X * Polynomial.X) := by
  rw [fₑ_eq_fₑ' (hchar := hchar)]
  unfold fₑ'
  rcases f with ⟨⟨supp, g, h⟩⟩
  simp
  apply Polynomial.ext
  intro n
  simp
  rw [←comp_x_sqrt_eq_deevenized]
  unfold deevenize
  simp
  unfold fₑ_x evenize
  rw [fₑ_eq_fₑ' (hchar := hchar)]
  unfold fₑ'
  simp
  by_cases hpar : n % 2 = 0
  · simp [hpar]
    rw [←Nat.div_add_mod n 2]
    rw [hpar]
    simp
  · simp [hpar]
    simp [even_iff_exists_two_mul]
    intros x h
    omega


lemma fₒ_x_is_a_subst_of_fₑ {f : Polynomial F} {hchar : (2 : F) ≠ 0} : fₒ f = (fₒ_x f).comp (Polynomial.X * Polynomial.X) := by
  rw [←fₒ_eq_fₒ' (hchar := hchar)]
  unfold fₒ'
  rcases f with ⟨⟨supp, g, h⟩⟩
  simp
  apply Polynomial.ext
  intro n
  simp
  rw [←comp_x_sqrt_eq_deevenized]
  unfold deevenize
  simp
  unfold fₒ_x evenize
  rw [←fₒ_eq_fₒ' (hchar := hchar)]
  unfold fₒ'
  simp
  by_cases hpar : n % 2 = 0
  · simp [hpar]
    rw [←Nat.div_add_mod n 2]
    rw [hpar]
    simp
  · simp [hpar]
    simp [even_iff_exists_two_mul]
    intros x h
    omega


lemma fₑ_x_eval {f : Polynomial F} {x : F} {hchar : (2 : F) ≠ 0} : Polynomial.eval (x ^ 2) (fₑ_x f) = Polynomial.eval x (fₑ f) := by
  have hh : Polynomial.eval (x ^ 2) (fₑ_x f) = Polynomial.eval (x) ((fₑ_x f).comp (Polynomial.X * Polynomial.X)) := by
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X]
    ring_nf
  rw [hh, ←fₑ_x_is_a_subst_of_fₑ]
  tauto

lemma fₒ_x_eval {f : Polynomial F} {x : F} {hchar : (2 : F) ≠ 0}: Polynomial.eval (x ^ 2) (fₒ_x f) = Polynomial.eval x (fₒ f) := by
  have hh : Polynomial.eval (x ^ 2) (fₒ_x f) = Polynomial.eval (x) ((fₒ_x f).comp (Polynomial.X * Polynomial.X)) := by
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X]
    ring_nf
  rw [hh, ←fₒ_x_is_a_subst_of_fₑ]
  tauto

lemma fₑ_is_even {f : Polynomial F} {s₀ s₁ : F} {h : s₀ * s₀ = s₁ * s₁ } {hchar : (2 : F) ≠ 0}:
  Polynomial.eval s₀ (fₑ f) = Polynomial.eval s₁ (fₑ f) := by
    rw [←fₑ_x_eval (hchar:=hchar), ←fₑ_x_eval (hchar:=hchar)]
    have hhh : s₀^2 = s₁ ^ 2 := by
        convert h <;> ring
    rw [hhh]


lemma fₒ_is_even' {f : Polynomial F} {s₀ s₁ : F} {h : s₀ * s₀ = s₁ * s₁ } {hchar : (2 : F) ≠ 0}:
  Polynomial.eval s₀ (fₒ f) = Polynomial.eval s₁ (fₒ f) := by
    rw [←fₒ_x_eval, ←fₒ_x_eval]
    have hhh : s₀^2 = s₁ ^ 2 := by
        convert h <;> ring
    rw [hhh]
    tauto
    tauto

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
  { h₂ : f.eval s₀ = α₀ } {h₃ : f.eval s₁ = α₁ } {h₄ : s₀ ≠ s₁ }{hchar : (2 : F) ≠ 0}
   :
  line_through_two_points (s₀, α₀) (s₁, α₁) =
    Polynomial.C (Polynomial.eval (s₀^2) (fₑ_x f)) + Polynomial.X * (Polynomial.C (Polynomial.eval (s₀^2) (fₒ_x f))) := by
  unfold line_through_two_points
  simp only [map_sub, map_mul, Polynomial.X_mul_C]
  apply Polynomial.ext
  intro n
  rcases n with _ | n <;> simp
  · rw [←h₂, ←h₃, fₑ_x_eval (hchar := hchar)]
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
        rw [←fₑ_plus_x_mul_fₒ_eq_f (f := f) (hchar := hchar)]
    rw [hhh]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    ring_nf
    rw [fₒ_is_even' (s₀ := s₀) (s₁ := s₁) (h := h₁) (hchar := hchar)]
    ring_nf
    rw [fₑ_is_even (s₀ := s₁) (s₁ := s₀) (h := by aesop) ]
    ring_nf
    intro contr
    have hhh : s₁ = s₀ := by
      have hhh : s₀ = s₀ + 0 := by
        ring_nf
      rw [hhh, ←contr]
      ring_nf
      rw [contr]
      simp
      tauto
    aesop
    intro contr
    have hhhh : s₁ = s₀ := by
      have hhh : s₀ = s₀ + 0 := by
        ring_nf
      rw [hhh, ←contr]
      ring_nf
    tauto
  · rcases n with _ | n <;> simp
    rw [←h₂, ←h₃, fₒ_x_eval (hchar := hchar)]
    rw [div_eq_iff]
    conv =>
      lhs
      rw [←fₑ_plus_x_mul_fₒ_eq_f (f := f) (hchar := hchar)]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    ring_nf
    rw [fₑ_is_even (s₀ := s₀) (s₁ := s₁) (h := h₁) (hchar:=hchar) ]
    ring_nf
    rw [fₒ_is_even' (s₀ := s₁) (s₁ := s₀) (h := by aesop) (hchar := hchar)]
    intro contr
    have hhh : s₁ = s₀ := by
      have hhh : s₀ = s₀ + 0 := by
        ring_nf
      rw [hhh, ←contr]
      ring_nf
    aesop

lemma consistency_check_comp { f : Polynomial F }  {x₀ : F} {y : F} {s₀ s₁ : F} {α₀ α₁ β : F} { h₁ : s₀ * s₀ = s₁ * s₁ }
  { h₂ : f.eval s₀ = α₀ } {h₃ : f.eval s₁ = α₁ } { h₄ : Polynomial.eval y (foldα f x₀)= β }
  { h₅ : s₀ * s₀ = y } {h₆ : s₀ ≠ s₁ } {hchar : (2 : F) ≠ 0}:
  consistency_check x₀ s₀ s₁ α₀ α₁ β = true := by
  unfold consistency_check
  simp
  rw [@line_passing_through_the_poly _ _ _ _ f s₀ s₁ α₀ α₁ h₁ h₂ (hchar :=  hchar) ]
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
