import tactic
import data.polynomial.basic
import data.polynomial.div
import data.nat.parity
open polynomial
open nat

noncomputable theory
open_locale classical

meta def ring_poly := `[
  apply polynomial.eq_of_subs,
  intro r,
  try {simp},
  try {ring}
]

variables {R : Type*} [field R] -- should work with comm_ring but some lemmas used for simp won't work

-- This lemma is false in general, we will fix this later
lemma polynomial.eq_of_subs (p q : polynomial R) : (∀ (r : R), p.eval r = q.eval r) → p = q :=
begin
  sorry
end

lemma induction_ppl_bit {P : ℕ → Prop} (m : ℕ) (h0 : P 0)
  (hbit0 : ∀ n, P n → P (2 * n)) (hbit1 : ∀ n, P n → P (2 * n + 1))
  : P m :=
begin
  apply nat.strong_induction_on m,
  have nat_is_pos : 0 ≤ m, exact nat.zero_le m,
  intros m hm,
  by_cases hz : m = 0,
  { rw hz, exact h0 },
  by_cases he : even m,
  {
    obtain ⟨k, rfl⟩ := he,
    rw ← two_mul,
    apply hbit0,
    apply hm k,
    have hk' : 0 < k,
    {apply nat.pos_of_ne_zero,
    intro hc, subst hc, contradiction},
    linarith,
  },
  {
    replace he : odd m := odd_iff_not_even.mpr he,
    obtain ⟨k, rfl⟩ := he,
    apply hbit1,
    apply hm k,
    linarith,
  }
end

variables (A B : R)

lemma nat_sub_add (n m k : ℕ) (h : m ≤ n) : n - m + (m + k) = n + k :=
by linarith

lemma nhalves {n m r : ℕ} :  n / 2 + m < n + m + r + 1 :=
begin
  have nhalf : n / 2 ≤ n := nat.div_le_self n 2,
  linarith,
end

lemma nhalves' {n m r : ℕ} : (n+1)/2 + m < n + m + r + 1:=
begin
  have nhalf : (n+1)/2 < n + 1 := div_lt_self' n 0,
  linarith,
end

/--
Define the "depleted" psi polynomials. They are Ψ as in Wikipedia,
but for even n we remove a factor of 2*y, thus making them one-variable.
-/
noncomputable def psi' : ℕ → (polynomial R) 
| 0 := (0 : polynomial R)
| 1 := (1 : polynomial R)
| 2 := (1 : polynomial R)
| 3 := (3 : R)•X^4 + (6*A)•X^2 + (12*B)•X - A^2•1
| 4 := (2 : R)•X^6 + (10*A)•X^4 + (40*B)•X^3-(10*A^2)•X^2-(8*A*B)•X- (2*A^3+16*B^2)•1
| (n+5) := 
  have n/2+4 < n+4+0+1 := nhalves,
  have n/2+3 < n+3+1+1 := nhalves,
  have n/2+2 < n+2+2+1 := nhalves,
  have n/2+1 < n+1+3+1 := nhalves,
  have (n+1)/2 < n+0+4+1 := @nhalves' _ 0 _,
  have (n+1)/2+1 < n+1+3+1 := nhalves',
  have (n+1)/2+2 < n+2+2+1 := nhalves',
  have (n+1)/2+3 < n+3+1+1 := nhalves',
  have (n+1)/2+4 < n+4+0+1 := nhalves',
  if even n then
    if even (n / 2) then
      ((4:R)•X^3+(4*A)•X+(4*B)•1)^2 * psi' (n/2+4) * (psi' (n/2+2))^3 - psi' (n/2+1) * (psi' (n/2+3))^3
    else 
      psi' (n/2+4) * (psi' (n/2+2))^3 - ((4:R)•X^3+(4*A)•X+(4*B)•1)^2 * psi' (n/2+1) * (psi' (n/2+3))^3
  else
      (psi' ((n+1)/2+2)) * ((psi' ((n+1)/2+4)) * (psi' ((n+1)/2+1))^2 -
        psi' ((n+1)/2) * (psi' ((n+1)/2+3))^2)

local notation `ψ'` := psi' A B

example : ψ' 3 = (3:R)•X^4 + (6*A)•X^2 + (12*B)•X - (A^2)•1 := by simp [psi']

example : ψ' 4 =  
(2:R)•X^6 + (10*A)•X^4 + (40*B)•X^3 - (10*A^2)•X^2 - (8*A*B)•X +(-2*A^3 - 16*B^2)•1
:=
begin
  unfold psi',
  ring_poly,
end


example : ψ' 5 =  
5*X^12 + 62*A•X^10 + 380*B•X^9 - 105*A^2•X^8 + (240*A*B)•X^7 + 
(-300*A^3 - 240*B^2)•X^6 - (696*A^2*B)•X^5 + (-125*A^4 - 1920*A*B^2)•X^4 + 
(-80*A^3*B - 1600*B^3)•X^3 + 
(-50*A^5 - 240*A^2*B^2)•X^2 + 
(-100*A^4*B - 640*A*B^3)•X + (A^6 - 32*A^3*B^2 - 256*B^4)•1
:=
begin
  simp [psi'],
  ring_poly,
end

/-
example : ψ' 6 = 
3*X^16 + 72*A•X^14 + 672*B•X^13 - 364*A^2•X^12 + (-1288*A^3 - 2688*B^2)•X^10 - (4576*A^2*B)•X^9 + 
(-942*A^4 - 19872*A*B^2)•X^8 + (768*A^3*B - 22272*B^3)•X^7 + (-1288*A^5 - 2688*A^2*B^2)•X^6 + 
(-3360*A^4*B - 16128*A*B^3)•X^5 + (-364*A^6 - 4032*A^3*B^2 - 5376*B^4)•X^4 + 
(-1792*A^5*B - 12544*A^2*B^3)•X^3 + (72*A^7 - 1536*A^4*B^2 - 13824*A*B^4)•X^2 + 
(96*A^6*B - 256*A^3*B^3 - 6144*B^5)•X + (3*A^8 + 96*A^5*B^2 + 512*A^2*B^4)•1
:=
begin
  simp [psi'],
  ring_poly,
end
 -/

lemma le_succ_of_le_and_ne {k m : ℕ} (h : m ≤ k) (h' : m ≠ k) : m+1 ≤ k :=
begin
  rw le_iff_lt_or_eq at h,
  cases h,
  { exact succ_le_iff.mpr h },
  { contradiction }
end

lemma add_two_div_two {k : ℕ} : (k + 2) / 2 = k / 2 + 1 := by simp

lemma even_odd_succ {k : ℕ} (h : even k) :¬ even (k+1) := by simp [even_add, h]

lemma odd_even_succ {k : ℕ} (h : odd k) :¬ odd (k+1) := by simp [odd_add, h]

@[simp]
lemma even_odd_succ_iff {k : ℕ} : even (k+1) ↔ odd k :=
  by simp [even_odd_succ, odd_even_succ, even_add]

@[simp]
lemma odd_even_succ_iff {k : ℕ} : odd (k+1) ↔ even k :=
  by simp [even_odd_succ, odd_even_succ, even_add]

/-- Duplication formula for Ψ' -/
lemma psi_bit0 {n : ℕ}  (h : 2 ≤ n) :
 ψ'(2*n) = ψ' n * ( ψ'(n+2) * ψ'(n-1)^2 - ψ'(n-2) * ψ'(n+1)^2 ) :=
begin
  have twopos : 0 < 2, by linarith,
  by_cases hedge : n = 2,
  {
    subst hedge,
    unfold psi',
    have : 2*2 = 4, by refl,
    simp [psi', this],
  },
  replace h : 3 ≤ n := le_succ_of_le_and_ne h (ne.symm hedge),
  by_cases he : even n,
  {
    let k := 2*n - 5,
    have hk : 2 * n = k + 5, by {rw nat.sub_add_cancel, linarith},
    have hkodd : ¬ even k,
    {
      rw ←nat.odd_iff_not_even,
      use (n-3),
      rw [nat.mul_sub_left_distrib, hk],
      norm_num,
      rw ←nat.sub_eq_iff_eq_add,
      linarith,
    },
    rw hk,
    have hn : n = (k+1)/2 + 2,
    {
      rw ←nat.sub_eq_iff_eq_add,
      {
        have hk' : 2*n-5 = k, by simp [hk],
        rw ←hk',
        suffices : 2*(n-2) = (2 * n - 5 + 1), by {rw [←@nat.mul_div_cancel (n-2) 2 twopos,←this], simp},
        rw nat.mul_sub_left_distrib,
        norm_num,
        simp [hk],
      },
      exact le_of_succ_le h,
    },
    simp [psi', hkodd, hn],
  },
  {
    let k := 2*n - 6,
    have hk : 2 * n = k + 6, by { rw nat.sub_add_cancel, linarith },
    rw hk,
    have hkeven : even k,
    {
      use (n-3),
      rw [nat.mul_sub_left_distrib, hk],
      norm_num,
    },
    have hn : n = (k+2)/2 + 2,
    {
      suffices : n = k / 2 + 3, by simp [this],
      rw ←nat.sub_eq_iff_eq_add h,
      {
        have hk' : 2*n-6 = k, by simp [hk],
        rw ←hk',
        suffices : 2*(n-3) = (2 * n - 6),
        {
          rw [←@nat.mul_div_cancel (n-3) 2 twopos, ←this],
          simp,
        },
        rw nat.mul_sub_left_distrib,
        norm_num,
      },
    },
    have hke : even (k/2),
    {
      obtain ⟨r, hr⟩ := odd_iff_not_even.mpr he,
      have : k/2 = n - 3, by simp [←nat.sub_add_cancel h, hr, hn],
      rw this,
      exact odd.sub_odd (odd_iff_not_even.mpr he) (odd_bit1 1),
    },
    change n = (k+1+1)/2 + 2 at hn,
    simp [psi', hkeven, hn],
  },
end

lemma even_nat_iff_coe  (a : ℕ) : even a ↔ even (a : ℤ) :=
begin
  split,
  {
    intro h,
    obtain ⟨k, hk⟩ := h,
    exact ⟨k, by linarith⟩,
  },
  {
    intro h,
    obtain ⟨k, hk⟩ := h,
    have hpos : 0 ≤ k, by linarith,
    rw ←(int.nat_abs_of_nonneg hpos) at hk,
    exact ⟨k.nat_abs, by {zify, exact hk}⟩,
  }
end

/-- Duplic-add-tion formula for Ψ' -/
lemma psi_bit1 {n : ℕ} (h : 1 ≤ n) :
 ψ'(2*n+1) = ψ' (n+2) * (ψ' n)^3 * (ite (even n) (16*(X^3 + A•X + B•1)^2) 1) - ψ' (n-1) * (ψ' (n+1))^3 * (ite (even n) 1 (16*(X^3 + A•X + B•1)^2)) :=
begin
  by_cases h0 : n = 1,
  {
    subst h0,
    have hone: odd 1 := odd_bit1 0,
    simp [psi', hone],
  },
  replace h : 2 ≤ n := le_succ_of_le_and_ne h (ne.symm h0),
  have twopos : 0 < 2, by linarith,
  by_cases hedge : n = 2,
  {
    subst hedge,
    unfold psi',
    have : 2*2 + 1 = 5, by refl,
    simp [psi', this],
    ring_poly,
  },
  replace h : 3 ≤ n := le_succ_of_le_and_ne h (ne.symm hedge),
  by_cases he : even n,
  {
    let k := 2 * n - 5,
    have hk : 2 * n = k + 5,
    {
      rw nat.sub_add_cancel,
      linarith,
    },
    rw hk,
    have hkodd : ¬ even k,
    {
      rw ←nat.odd_iff_not_even,
      use (n-3),
      rw [nat.mul_sub_left_distrib, hk],
      norm_num,
      rw ←nat.sub_eq_iff_eq_add,
      linarith,
    },
    have hn : n = (k+1)/2 + 2,
    {
      rw ←nat.sub_eq_iff_eq_add,
      {
        have hk' : 2*n-5 = k, by simp [hk],
        rw ←hk',
        suffices : 2*(n-2) = (2 * n - 5 + 1),
        {
          rw [←@nat.mul_div_cancel (n-2) 2 twopos,←this],
          simp,
        },
        rw nat.mul_sub_left_distrib,
        norm_num,
        simp [hk],
      },
      linarith,
    },
    rw hn,
    have hs1 : (k + 1) / 2 + 2 + 2 = (k + 1) / 2 + 4 := by linarith,
    have hs2 : (k + 1) / 2 + 2 - 1 = (k + 1) / 2 + 1 := by {zify, simp},
    have hk' : even ((k+1) / 2),
    {
      obtain ⟨r, hr⟩ := he,
      zify at hr,
      rw even_nat_iff_coe,
      have : even ((k + 1)/2 : ℤ) := ⟨r-1, by linarith⟩,
      exact this,
    },
    simp [psi', hkodd, hk', he, hs1, hs2],
    ring_poly,
  },
  {
    have twon_ge_six : 6 ≤ 2 * n, by linarith [h],
    simp [he],
    let k := 2 * n - 6,
    have hk : 2 * n + 1 = k + 7,
    {
      rw ←nat_sub_add,
      exact twon_ge_six,
    },
    rw hk,
    have hkeven : even k,
    {
      use (n-3),
      zify at hk ⊢,
      replace hk : (k : ℤ) = 2 * n + 1 - 7, by linarith,
      rw hk,
      have : (((n-3) : ℕ) : ℤ) = (n : ℤ) - 3 := int.of_nat_sub h,
      rw this,
      ring,
    },
    have hn : n = (k+2)/2 + 2,
    {
      suffices : n = k / 2 + 3, by simp [this],
      rw ←nat.sub_eq_iff_eq_add h,
      {
        have : 2*n-6+6+1 = k + 6+1, by rw [nat.sub_add_cancel twon_ge_six, hk],
        have hk' : 2*n-6 = k, by linarith [this],
        rw ←hk',
        suffices : 2*(n-3) = (2 * n - 6),
        {
          rw [←@nat.mul_div_cancel (n-3) 2 twopos, ←this],
          simp,
        },
        rw nat.mul_sub_left_distrib,
        norm_num,
      },
    },
    have hke : even (k/2),
    {
      obtain ⟨r, hr⟩ := odd_iff_not_even.mpr he,
      have : k/2 = n - 3, by simp [←nat.sub_add_cancel h, hr, hn],
      rw this,
      exact odd.sub_odd (odd_iff_not_even.mpr he) (odd_bit1 1),
    },
    have hs1 : (k / 2).succ + 1 = (k / 2) + 2, by refl,
    have hs2 : (k / 2).succ + 2 + 1 = (k / 2).succ + 3, by refl,
    simp [psi', hke, hn, hkeven, hs1, hs2],
    ring_poly,
  },
end

/-- Duplic-sub-tion formula for Ψ' -/
lemma psi_bit1' {n : ℕ}  (h : 2 ≤ n) :
 ψ'(2*n-1) = ψ' (n+1) * (ψ' (n-1))^3 * (ite (even n) 1 (16*(X^3 + A•X + B•1)^2)) - ψ' (n-2) * (ψ' (n))^3 * (ite (even n) (16*(X^3 + A•X + B•1)^2) 1) :=
begin
  have H : ∃ m, (1≤ m) ∧ n = m+1,
  {
    use n-1,
    split,
    { exact le_tsub_of_add_le_left h },
    { have h' : 1 ≤ n := le_of_succ_le h,
      rw nat_sub_add _ _ 0 h',
      refl }
  },
  obtain ⟨m, ⟨hm, rfl⟩⟩ := H,
  have h1 : 2 * (m + 1) - 1 = 2*m +1, by omega,
  rw [h1,psi_bit1 _ _ hm],
  simp,
end

-- This is really ψ^2 from the Wikipedia definition.
def psisq (n : ℕ) := 
  (psi' A B n)^2 * (ite (even n) (4 * (X^3 + A•X + B•1)) 1)

local notation `ψ2` := psisq A B

lemma psisq_def {n : ℕ} (he : even n) : ψ2 n = (psi' A B n)^2 * (4 * (X^3 + A•X + B•1)) :=
by simp [he, psisq]

lemma psisq_def' {n : ℕ} (he : ¬ even n) : ψ2 n = (psi' A B n)^2 :=
by simp [he, psisq]

/-- Duplication formula for Ψ2 -/
lemma psisq_bit0 {n : ℕ} (h : 2 ≤ n) (he : even n) :
 ψ2 (2*n) = ψ2 n * ( ψ'(n+2) * ψ2 (n-1) - ψ'(n-2) * ψ2 (n+1) )^2 :=
begin
  have het : even (2*n) := even_two_mul n,
  unfold psisq,
  have hen' : ¬ even (n+1) := even_odd_succ he,
  have hen'' : ¬ even (n-1) :=
  begin
    rw ←odd_iff_not_even at hen' ⊢,
    suffices : odd (n + 1 - 2), by exact this,
    rw odd_sub (le_add_right h),
    have even_two := even_two_mul 1,
    tauto,
  end,
  rw psi_bit0 A B h,
  simp [he, het, hen', hen''],
  ring,
end

/-- Duplic-add-tion formula for Ψ2 -/
lemma psisq_bit1 {n : ℕ} (h : 1 ≤ n) (he : even n) :
ψ2 (2*n+1) = (ψ' (n+2) * (ψ' n)^3 * (16*(X^3 + A•X + B•1)^2) - ψ' (n-1) * ψ' (n+1)^3 )^2 :=
begin
  unfold psisq,
  have het : even (2*n) := even.mul_left he _,
  simp [he, het],
  congr' 1,
  rw psi_bit1 _ _ h,
  simp [he, het],
end


-- This is φ n from the Wikipedia
noncomputable def phi (n : ℕ) : polynomial R
:= X * ψ2 n - ψ'(n+1) * ψ'(n-1) * (ite (even n) 1 (4 * (X^3 + A•X + B•1)))

local notation `φ` := phi A B

-- This is 2ω when n is even, and y⁻¹ω when n is odd (ω as in Wikipedia)
noncomputable def omega' (n : ℕ) : polynomial R
:= ψ'(n+2) * ψ' (n-1)^2 - ψ'(n-2) * ψ' (n+1)^2

local notation `ω'` := omega' A B

lemma omega'_def (n : ℕ): ω' n = ψ'(n+2) * ψ' (n-1)^2 - ψ'(n-2) * ψ' (n+1)^2 := rfl

lemma omega'_def' (n : ℕ): ω' n * (4 * (X^3 + A•X + B•1)) =
ψ'(n+2) * (ψ' (n-1)^2 * (4 * (X^3 + A•X + B•1))) - ψ'(n-2) * (ψ' (n+1)^2 * (4 * (X^3 + A•X + B•1))):=
begin
  rw omega'_def,
  ring,
end

/-- Duplication formula for Ψ2, second version -/
lemma psisq_bit0' {n : ℕ}  (h : 2 ≤ n) (he : ¬ even n) :
 ψ2 (2*n) * (4 * (X^3 + A•X + B•1)) =  ψ2 n * ( ψ'(n+2) * ψ2 (n-1) - ψ'(n-2) * ψ2 (n+1) )^2 :=
begin
  have het : even (2*n) := even_two_mul n,
  unfold psisq,
  have hen' : even (n+1) := even_succ.mpr he,
  have hen'' : even (n-1) := odd.sub_odd (even_odd_succ_iff.mp hen') (odd_bit1 0),
  simp [he, het, hen', hen''],
  rw psi_bit0 A B h,
  ring,
end

/-- Duplic-add-tion formula for ψ2, second version -/
lemma psisq_bit1' {n : ℕ} (h : 1 ≤ n) (he : ¬ even n) :
ψ2 (2*n+1) = (ψ' (n+2) * (ψ' n)^3 - ψ' (n-1) * ψ' (n+1)^3 * (16*(X^3 + A•X + B•1)^2))^2 :=
begin
  unfold psisq,
  have het : even (2*n) := even.mul_left (nat.even_bit0 1) _,
  simp [he, het],
  congr' 1,
  rw psi_bit1 _ _ h,
  simp [he, het],
end

lemma psi_double {n : ℕ} (h : 2 ≤ n) : ψ' (2*n) = ψ' n * ω' n :=
begin
  rw psi_bit0 _ _ h,
  unfold omega',
end
 
/-- Useful unification of statements -/
def omega_sq (n : ℕ) : polynomial R :=
  (omega' A B n)^2 * (ite (even n) 1 (4 * (X ^ 3 + A • X + B • 1)))

local notation `ω2` := omega_sq A B 

lemma omega_sq_def {n : ℕ} : ω2 n =
(omega' A B n)^2 * (ite (even n) 1 (4 * (X ^ 3 + A • X + B • 1))) := rfl

lemma psisq_bit0_omegasq {n : ℕ} (h : 2 ≤ n) : ψ2 (2*n) = ψ2 n * ω2 n :=
begin
  unfold psisq,
  unfold omega_sq,
  have ht : even (2 * n) := even.mul_left (nat.even_bit0 1) _,
  by_cases he : even n;
  {
    simp [he, ht],
    rw psi_double _ _  h,
    ring,
  },
end


lemma psi_simp (n : ℕ) : psi' A B (2 * (n + 1) - 1) = psi' A B (2*n+1) := by congr
lemma psi_simp' (n : ℕ) : psi' A B (n + 1 + 2) = psi' A B (n + 3) := by congr
lemma psi_simp'' (n : ℕ) : psi' A B (n + 1 + 1) = psi' A B (n + 2) := by congr

-- duplication formula is: if P=(x,y), then
-- x(2P) = (9*x^4 + 6*A*x^2 - 8*x*y^2 + A^2)/(4*y^2) = (x^4 - 2*A*x^2 - 8 * B * x + A^2) / (4*y^2)
-- y(2P) = (-27*x^6 - 27*A*x^4 + 36*x^3*y^2 - 9*A^2*x^2 + 12*A*x*y^2 - 8*y^4 - A^3)/(8*y^3)
-- This gives a certain identity between polynomials in x of degree 12.
example {n : ℕ} (h : n < 2) : n = 0 ∨ n = 1 := by omega

lemma psisq_bit0_even {n : ℕ} (hn : 2 ≤ n) (he : even n)
(hc : ω2 n = φ n^3 + A • φ n * ψ2 n ^ 2 + B • ψ2 n ^ 3 ) :
ψ2 (2*n)  = ψ2 n * ((φ n)^3 + A • φ n * (ψ2 n)^2 + B • (ψ2 n)^3) :=
begin
  simp [he, psisq_bit0 A B hn he],
  have he' : ¬ even (n - 1),
  { rw ←odd_iff_not_even,
    apply even.sub_odd (le_of_succ_le hn) he (odd_bit1 0) },
  simp [psisq, he, he'],
  rw ←omega'_def,
  rw ←psisq_def _ _ he,
  suffices :  omega' A B n ^ 2 = phi A B n^ 3 + A • phi A B n * psisq A B n^2 + B • psisq A B n^3,
  by rw this,
  rw ←hc,
  simp [omega_sq_def, he],
end

lemma psisq_bit0_odd {n : ℕ} (hn : 2 ≤ n) (he : ¬ even n)
(hc : ω2 n * (4 * (X^3 + A•X + B•1))  = φ n^3 + A • φ n * ψ2 n ^ 2 + B • ψ2 n ^ 3 ) :
ψ2 (2*n) * (4 * (X^3 + A•X + B•1)) = ψ2 n * ((φ n)^3 + A • φ n * (ψ2 n)^2 + B • (ψ2 n)^3) :=
begin
  simp [he, psisq_bit0' A B hn he],
  have he' : even (n - 1) :=
    odd.sub_odd (odd_iff_not_even.mpr he) (odd_bit1 0),
  simp [psisq, he, he'],
  rw ←omega'_def',
  rw ←psisq_def' _ _ he,
  suffices :  (omega' A B n * (4 * (X ^ 3 + A • X + B • 1))) ^ 2 
  = phi A B n^ 3 + A • phi A B n * psisq A B n^2 + B • psisq A B n^3,
    by rw this,
  rw ←hc,
  simp [omega_sq_def, he],
  ring,
end

/-- A formula for relating ψ2(2*n) / ψ2^4 to φ / ψ2 involving φ. Valid for all n ≥ 2 -/
theorem psisq_bit0_inductive {n : ℕ} (hn : 2 ≤ n)
(hc : (ω2 n * (ite (even n) 1 (4 * (X ^ 3 + A • X + B • 1)))) = φ n^3 + A • φ n * ψ2 n ^ 2 + B • ψ2 n ^ 3 ) :
ψ2 (2*n) * (ite (even n) 1  (4 * (X^3 + A•X + B•1))) = ψ2 n * ((φ n)^3 + A • φ n * (ψ2 n)^2 + B • (ψ2 n)^3) :=
begin
  by_cases he : even n,
  { simp [he] at hc ⊢,
    apply psisq_bit0_even _ _ hn he hc },
  { simp [he] at hc ⊢,
    apply psisq_bit0_odd _ _ hn he hc }
end

/-
Now we will study the degrees and leading terms.
-/

example : (X : polynomial R).degree = 1 := degree_X

example (n : ℕ) : ((X : polynomial R)^n).degree = n :=
begin
  finish,
end


lemma deg_psip {n : ℕ} :
(ψ' n).nat_degree = ite (even n) ((n^2-4) / 2) ((n^2-1) / 2) :=
begin
  apply @nat.strong_induction_on (λ n, (ψ' n).nat_degree = ite (even n) ((n^2-4) / 2) ((n^2-1) / 2)),
  rintros m hm,
  clear n,
  simp at hm,
  by_cases h0 : m = 0,
  {
    subst h0,
    simp [psi'],
  },
  by_cases h1 : m = 1,
  {
    subst h1,
    simp [psi'],
  },
  by_cases h2 : m = 2,
  {
    subst h2,
    simp [psi'],
    ring,
  },
  by_cases h3 : m = 3,
  {
    subst h3,
    simp [psi'],
    have htmp : (3^2 -1)/2 = 4, by sorry,
    rw htmp,
    sorry,
  },
  have hm : 4 ≤ m,
  {
    sorry
  },
  clear h0 h1,
  by_cases he : even m,
  {
    simp [he],
    obtain ⟨k, hk⟩ := he,
    subst hk,
    replace hm : 2 ≤ k, by linarith,
    rw psi_bit0 _ _ hm,
    sorry
  },
  {
    sorry
  }
end
