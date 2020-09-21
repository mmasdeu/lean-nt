import group_theory.subgroup
import group_theory.coset
import data.fintype.card
import data.set.finite
import data.zmod.basic
import algebra.gcd_monoid
import basic
import tactic

open_locale classical big_operators
noncomputable theory

-- set_option profiler true

variables {p r n m: ℕ}-- [fact p.prime] [0 < n] [0 < m] [1 ≤ r]

def C2 (k : ℕ) : subgroup (units (zmod k)) :=
{
    carrier := {1, -1},
    one_mem' := by simp,
    mul_mem' := λ a b (ha : a ∈ {1, -1}) (hb : b ∈ {1, -1}), by finish,
    inv_mem' := λ a (ha : a ∈ {1, -1}), by finish,
}

lemma pr_eq_p_mul_pr1 (h : 1 ≤ r) : p^r = p * p^(r-1) :=
begin
    induction r with d hd,
    linarith,
    ring
end

lemma zero_iff_n_divides (x : zmod n) (h : 0 < n) : x = 0 ↔ n  ∣ x.val :=
begin
    split,
    {
        intro h,
        finish,
    },
    {
        intro h,
        cases h with w hw,
        suffices : w = 0, by finish,
        {
            haveI : fact(0 < n) := h,
            have H : x.val < n := zmod.val_lt x,
            rw hw at H,
            suffices : w < 1, by linarith,
            exact (mul_lt_iff_lt_one_right h).mp H,
        }
    }
end

lemma zero_iff_n_divides' (x : ℤ) : (x : zmod n) = 0 ↔ (n : ℤ) ∣ x := char_p.int_cast_eq_zero_iff (zmod n) n x

lemma eq_iff_n_divides' {x y : ℤ} (hp: p.prime) : (x : zmod (p^r)) = y ↔ (p^r : ℤ) ∣ x - y :=
begin
    haveI hp_prime : p.prime := by assumption,
    haveI pr_pos : 0 < p^r := nat.pos_pow_of_pos r (nat.prime.pos hp_prime),
    split,
    {
        intro h,
        have h' : (((x - y) : ℤ) : zmod (p^r)) = 0,
        {
            rw← sub_eq_zero at h,
            finish,
        },
        apply_mod_cast (char_p.int_cast_eq_zero_iff (zmod (p^r)) (p^r) (x-y)).mp h',
    },
    {
        intro h,
        suffices : (((x - y) : ℤ) : zmod (p^r)) = 0,
        {
            rw←  sub_eq_zero,
            finish,
        },
        replace h : ((p^r : ℕ) : ℤ) ∣ (x - y),
        {
            finish,
        },
        exact_mod_cast (char_p.int_cast_eq_zero_iff (zmod (p^r)) (p^r) (x-y)).mpr h,
    }
end

lemma coerce_down (x y: zmod (p^r)) (h : x = y) : (x : zmod p) = (y : zmod p) :=
    by exact congr_arg coe h

lemma key_lemma (x : ℤ) (h : (x : zmod (p^r))^2 = 1) (hr : 1 ≤ r) (hp : p.prime) : (x : zmod p) = 1 ∨ (x : zmod p) = -1 :=
begin
    rw ←sub_eq_zero at h,
    rw_mod_cast zmod.int_coe_zmod_eq_zero_iff_dvd at h,
    have h_p_dvd : (p : ℤ) ∣ (x - 1) * (x + 1),
    {
        obtain ⟨w, hw⟩ := h,
        ring,
        rw hw,
        refine dvd_mul_of_dvd_left _ w,
        casesI r,
        exact absurd nat.one_pos (not_lt_of_le hr),
        {
            use p^r,
            exact int.coe_nat_pow p (r + 1),
        }
    },
    have h3 := (int.prime.dvd_mul' hp h_p_dvd),
    simpa [←zmod.int_coe_zmod_eq_zero_iff_dvd, ←sub_eq_zero] using h3,
end

lemma part1 {x ε : ℤ} (hprime : p.prime) (one_le_r : 1 ≤ r)
    (h : (x : zmod (p^r))^2 = 1) (h_odd : 2 < p) (h_eps : ε = 1 ∨ ε = -1) :
    (x : zmod p) = ε → (p^r : ℤ) ∣ (x-ε) :=
begin
    haveI p_ne_zero : (p : ℤ) ≠ 0 :=
        by exact_mod_cast nat.prime.ne_zero hprime,
    haveI p_pos : 0 < p := nat.prime.pos hprime,
    haveI pr_pos : 0 < p^r := nat.pos_pow_of_pos r (nat.prime.pos hprime),
    have h_prdiv : (p^r : ℤ) ∣ (x^2 - 1),
    {
        rw ←eq_iff_n_divides' hprime,
        exact_mod_cast h,
    },
    have h_fact : (p^r : ℤ) = p * p^(r-1),
        by exact_mod_cast pr_eq_p_mul_pr1 one_le_r,
    obtain ⟨ f, hf ⟩ := h_prdiv,
    intro hp,
    replace hp : ((x - ε :ℤ) : zmod p) = 0, by exact_mod_cast sub_eq_zero.mpr hp,
    rw zero_iff_n_divides' at hp,
    cases hp with e he,
    suffices : (p^(r-1) : ℤ) ∣ e,
    {
        cases this with f hf,
        use f,
        rw [he, hf, ←mul_assoc, ←h_fact],
    },
    have hcalc :=
        calc
        (p : ℤ) * (p ^ (r-1) * f) = p^r * f : by rw [←mul_assoc, h_fact]
        ...    = x^2 - 1 : by rw hf
        ...    = x^2 - ε^2 :
        begin
            rcases h_eps with rfl | rfl;
            simp only [one_pow, int.coe_nat_zero, int.coe_nat_succ, int.of_nat_eq_coe, zero_add, neg_square],
        end
        ...    = (x-ε)^2 + 2*ε*(x-ε) : by ring
        ...    =  (p * e)^2 + 2 * ε * (p*e) : by rw he at *
        ...    = p * (2 * ε * e + p * e^2)  : by ring,
    rw mul_right_inj' p_ne_zero at hcalc,
    replace hcalc : (p^(r-1) : ℤ) ∣ 2 * ε * e + p * e^2 := dvd.intro f hcalc,
    rw [mul_comm, mul_comm (p : ℤ), pow_two, mul_assoc, ←mul_add e] at hcalc,
    have p_not_dvd_2pe : ¬ (p : ℤ) ∣ (2 * ε + e * p),
    {
        rintro ⟨ s, hs ⟩,
        have p_dvd_2 : (p : ℤ)∣ 2,
        {
            use ε * (s-e),
            rw mul_sub,
            rcases h_eps with rfl | rfl;
            {
                ring,
                simp only [mul_one, mul_sub, int.mul_neg_eq_neg_mul_symm, neg_sub_neg, ←hs],
                ring,
            },
        },
        replace p_dvd_2 := int.dvd_nat_abs_of_of_nat_dvd p_dvd_2,
        rw_mod_cast nat.prime_dvd_prime_iff_eq hprime nat.prime_two at p_dvd_2,
        rw p_dvd_2 at h_odd,
        exact nat.lt_asymm h_odd h_odd,
    },
    have h_coprime : (p^(r-1)).coprime (2 * ε + e * p).nat_abs,
    {
        suffices : p.coprime (2 * ε + e *p).nat_abs, from nat.coprime.pow_left (r - 1) this,
        refine (nat.prime.coprime_iff_not_dvd hprime).mpr _,
        intro hc,
        apply p_not_dvd_2pe,
        simpa [←int.coe_nat_dvd_left, mul_comm] using hc,
    },
    have pow_div_abs : p^(r-1) ∣ e.nat_abs,
    {
        apply nat.coprime.dvd_of_dvd_mul_right h_coprime,
        obtain ⟨s, hs⟩ := hcalc,
        use s.nat_abs,
        rw [←int.nat_abs_mul, hs, int.nat_abs_mul],
        norm_cast,
    },
    obtain ⟨ t, ht ⟩ := pow_div_abs,
    use (t * e.sign),
    replace ht : e.sign * abs e = p^(r-1) * (t * e.sign),
    {
        rw [int.abs_eq_nat_abs, ht],
        simp only [int.coe_nat_pow, int.coe_nat_mul],
        ring,
    },
    simpa [int.sign_mul_abs e] using ht,
end

lemma pr_dvd_xm1_or_xp1 (x : ℤ) (hprime : p.prime) (one_le_r : 1 ≤ r)
    (h : (x : zmod (p^r))^2 = 1) (h_odd : 2 < p) :
    (p^r : ℤ) ∣ (x - 1) ∨ (p^r : ℤ) ∣ (x + 1) :=
begin
    have : (x + 1) = x - (-1), by ring,
    refine (@@key_lemma x h one_le_r hprime).imp _ _;
    {
        intro H,
        try { rw this },
        apply @@part1 hprime one_le_r h h_odd,
        dec_trivial,
        exact_mod_cast H,
    },
end

lemma two_torsion_subgroup_of_primepow (hp : p.prime) (one_le_r : 1 ≤ r) (h_odd : 2 < p) :
    two_torsion_subgroup (units (zmod (p^r))) = C2 (p^r) :=
begin
    ext1 x,
    fconstructor,
    {
        intro hx,
        change x * x = 1 at hx,
        unfold C2 at ⊢,
        suffices h : x = 1 ∨ x = -1, by assumption,
        have e_lift : ∃ (x' : ℤ), (x' : zmod (p^r)) = x, by apply zmod.int_cast_surjective,
        cases e_lift with x' hx',
        have pr_dvd_xpm1 : (p^r : ℤ) ∣ (x' - 1) ∨ (p^r : ℤ) ∣ (x' + 1),
        {
            apply pr_dvd_xm1_or_xp1 x' hp one_le_r,
            {
                rw [hx', pow_two],
                injections_and_clear,
                assumption,
            },
            exact h_odd,
        },
        cases pr_dvd_xpm1,
        left,
        swap,
        right,
        all_goals
        {
            ext1,
            try {rw ←sub_neg_eq_add at pr_dvd_xpm1},
            rw ←eq_iff_n_divides' at pr_dvd_xpm1,
            rw [←hx', pr_dvd_xpm1],
            norm_num,
            exact hp,
        },
    },
    {
        intro hx,
        ext1,
        cases hx; finish,
    },
end
