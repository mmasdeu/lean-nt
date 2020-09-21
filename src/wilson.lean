import group_theory.subgroup
import group_theory.coset
import data.fintype.card
import data.set.finite
import data.zmod.basic
import algebra.gcd_monoid
import first_lemmas
import tactic

open_locale classical big_operators
noncomputable theory

-- set_option profiler true

variables {p r n m: ℕ}

lemma is_fintype_C2 : fintype (C2 m) := by exact set.fintype_insert 1 {-1}

lemma one_neq_minus_one' (h : 2 < m) : (1 : (zmod m)) ≠ (-1 : (zmod m)) :=
begin
    intro h1,
    rw eq_neg_iff_add_eq_zero at h1,
    norm_num at h1,
    replace h1 : ((2 : ℤ) : zmod m) = 0, by finish,
    rw zero_iff_n_divides' at h1,
    replace h1 : m ∣ 2 := int.coe_nat_dvd.mp h1,
    rw nat.dvd_prime_two_le nat.prime_two (le_of_lt h) at h1,
    rw h1 at h,
    exact nat.lt_asymm h h,
end

lemma one_neq_minus_one (h : 2 < m) : (1 : units (zmod m)) ≠ (-1 : units(zmod m)) :=
begin
    intro h1,
    apply one_neq_minus_one' h,
    simpa [←units.eq_iff] using h1,
end

lemma two_torsion_subgroup_has_two_elements (h : 2 < m) [fintype (C2 m)] :
   fintype.card (C2 m) = 2 :=
begin
    let S : finset (units (zmod m)) := {1, -1},
    have H : ∀ x : units (zmod m), x ∈ S ↔ x ∈ C2 m,
    {
        intro x,
        split;
        {
            intro hx,
            try {replace hx : x = 1 ∨ x = -1, by assumption,},
            finish,
        },
    },
    suffices : finset.card S = 2,
    {
        rw ←this,
        exact fintype.card_of_subtype S H,
    },
    have h1 : ∀ (x : units (zmod m)), ∀ (T : finset(units(zmod m))), (x ∉ T → finset.card (insert x T) = finset.card T + 1),
    {
        intros x T hx,
        exact finset.card_insert_of_not_mem hx,
    },
    have h2 : ∀ (x y: units (zmod m)), x ≠ y → x ∉ {y} := λ {a b : units (zmod m)}, finset.not_mem_singleton.mpr,
    specialize h2 1 (-1) (one_neq_minus_one h),
    let S' : finset (units (zmod m)) := {-1},
    specialize h1 1 S' h2,
    assumption,
end

theorem prod_units_zmod_pr_eq_minus_one (hp : nat.prime p) (h_odd : 2 < p) (hr : 1 ≤ r) [fintype(units(zmod(p^r)))] :
    (∏ x : units (zmod(p^r)), x) = -1 :=
begin
    have hp : nat.prime p, by assumption,
    have hpr : 2 < p^r,
    {
        rw pr_eq_p_mul_pr1 hr,
        have H : 1 ≤ p^(r-1) := nat.pow_pos (nat.prime.pos hp) (r-1),
        rw [←mul_le_mul_left (nat.prime.pos hp), mul_one] at H,
        exact lt_of_lt_of_le h_odd H,
    },
    have h1 : fintype.card (two_torsion_subgroup (units (zmod (p^r)))) = 2,
    {
        rw two_torsion_subgroup_of_primepow hp hr h_odd,
        rw two_torsion_subgroup_has_two_elements hpr,
    },
    have h2 : (-1 : units (zmod(p^r))) * -1 = 1, by norm_num,
    rw [prod_identity_general (one_neq_minus_one hpr).symm h2, h1],
    simp only [nat.succ_pos', gt_iff_lt, pow_one, nat.div_self],
end