import group_theory.subgroup
import data.set.finite
import group_theory.coset
import data.fintype.card
import data.set.finite
import tactic

open_locale classical big_operators
noncomputable theory
-- set_option profiler true

lemma prod_finset_distinct_inv {α : Type*} [comm_group α] {s : finset α} :
  (∀ x ∈ s, x⁻¹ ∈ s) → (∀ x ∈ s, x⁻¹ ≠ x) → (∏ x in s, x) = 1 :=
begin

apply finset.case_strong_induction_on s,
tauto,
intros a s a_notin_s H h1 h2,
specialize H (finset.erase s a⁻¹) (finset.erase_subset (a⁻¹) s),
have r : (∏ x in (finset.erase s a⁻¹), x) = 1,
{
  apply H,
  {
    intros x h,
    suffices : ¬x = a ∧ x⁻¹ ∈ s, by simpa,
    split,
    {
      have x_in_s : x ∈ s := finset.mem_of_mem_erase h,
      by_contradiction,
      rw a_1 at x_in_s,
      exact a_notin_s x_in_s,
    },
    suffices : x⁻¹ ≠ a, from finset.mem_of_mem_insert_of_ne (h1 x (finset.mem_insert_of_mem (finset.mem_of_mem_erase h))) this,  
    by_contradiction hh,
    push_neg at hh,
    induction hh,
    simpa using finset.ne_of_mem_erase h,
  },
  {
    intros x h,
    apply h2,
    exact finset.mem_insert_of_mem (finset.mem_of_mem_erase h)
  }
},
{
  rw finset.prod_insert a_notin_s,
  suffices hkey : (∏ x in s, x) = a⁻¹,
  exact mul_eq_one_iff_inv_eq.mpr (eq.symm hkey),
  have ainv_notin_s1 : a⁻¹ ∉ finset.erase s a⁻¹ := finset.not_mem_erase a⁻¹ s,
  have ainv_in_s : a⁻¹ ∈ s,
  {
    have ainv_in_s1 : a⁻¹ ∈ insert a s := h1 a (finset.mem_insert_self a s),
    suffices : a⁻¹ ≠ a, from finset.mem_of_mem_insert_of_ne ainv_in_s1 this,
    exact h2 a (finset.mem_insert_self a s)
  },
  {
    rw [←finset.insert_erase ainv_in_s,finset.prod_insert ainv_notin_s1,r],
    exact mul_one a⁻¹
  },
},
end

lemma prod_eq_one_of_non_twotorsion {G : Type*} [comm_group G] [fintype G] : (∏ g in {x : G | x ≠ x⁻¹ }.to_finset, g) = 1 :=
begin
  apply prod_finset_distinct_inv;
  finish,
end


def two_torsion_subgroup (G : Type*) [comm_group G] : subgroup G :=
{ carrier := {z : G | z * z = 1},
  one_mem' := by simp,
  mul_mem' := λ a b (ha : a * a = 1) (hb : b * b = 1),
  begin
    dsimp at *,
    rw [mul_mul_mul_comm a b a b, ha, hb],
    refine mul_one 1,
  end,
  inv_mem' := λ a (ha : a * a = 1), by {tidy, rw mul_inv_eq_one, refine inv_eq_of_mul_eq_one ha}
}

lemma mem_two_torsion_iff_square_eq_one (G : Type*) [comm_group G] :
∀ x : G, x ∈ two_torsion_subgroup G ↔ x * x = 1 :=
begin
  intro x,
  refl,
end

lemma twotorsion_disjoint_non_twotorsion {G : Type*} [comm_group G]:
disjoint {x : G | x ∈ two_torsion_subgroup G} {x : G | x ≠ x⁻¹} :=
begin
    intros x hx,
    cases hx with h1 h2,
    have hA : x * x = 1, by assumption,
    suffices hB : x * x ≠ 1, by exact h2 (false.rec (x = x⁻¹) (hB hA)),
    simpa [← mul_eq_one_iff_eq_inv] using h2,
end

lemma prod_all_eq_prod_two_torsion {G : Type*} [comm_group G] [fintype G]:
(∏ g : G, g) = (∏ g : two_torsion_subgroup G, g) :=
begin
    have H : (∏ (g : G), g) = (∏ x in {x : G | x ∈ two_torsion_subgroup G}.to_finset, x)
            * (∏ x in {x : G | x ≠ x⁻¹ }.to_finset, x),
    {
        rw ← finset.prod_union,
        {
            congr, ext, safe,
            suffices hh : a ∈ two_torsion_subgroup G, tauto,
            have a2: a * a = 1 := eq_inv_iff_mul_eq_one.mp h,
            tauto,
        },
        {
            apply finset.disjoint_iff_disjoint_coe.2,
            simpa using twotorsion_disjoint_non_twotorsion,
        },
    },
    {
        simp [H, prod_eq_one_of_non_twotorsion],
        apply finset.prod_subtype,
        finish,
    },
end

lemma two_products_id {α: Type*} {s : set α} [fintype s] [comm_monoid α] {t : finset α}
 (h: ∀ x, x ∈ s ↔ x ∈ t) : (∏ g : s, ↑g) = (∏ g in t, g) := 
begin
refine finset.prod_bij (λ x _, x.1) _ _ _ _,
{
  intros a ha,
  specialize h a,
  apply h.mp,
  exact subtype.mem a,
},
{
  intros a ha,
  refl,
},
{
  intros a1 a2 h1 h2,
  exact subtype.eq,
},
{
  intros b hb,
  specialize h b,
  use b,
  rw h,
  exact hb,
  split,
  apply finset.mem_univ,
  exact rfl,
}
end

lemma two_products {α β: Type*} {s : set α} [fintype s] [comm_monoid β] {t : finset α} {f : α → β}
 (h: ∀ x, x ∈ s ↔ x ∈ t) : (∏ g : s, f g) = (∏ g in t, f g) := 
begin
refine finset.prod_bij (λ x _, x.1) _ _ _ _,
{
  intros a ha,
  specialize h a,
  apply h.mp,
  exact subtype.mem a,
},
{
  intros a ha,
  refl,
},
{
  intros a1 a2 h1 h2,
  exact subtype.eq,
},
{
  intros b hb,
  specialize h b,
  use b,
  rw h,
  exact hb,
  split,
  apply finset.mem_univ,
  exact rfl,
}
end

lemma prod_all_eq_prod_two_torsion' {G : Type*} [comm_group G] [fintype G]:
(∏ g : G, g) =  (∏ g in ((two_torsion_subgroup G) : set G).to_finset, g) :=
begin
  rw prod_all_eq_prod_two_torsion,
  have h : ((two_torsion_subgroup G) : set G).to_finset = (two_torsion_subgroup G).carrier.to_finset,
  {
      refl,
  },
  apply two_products_id,
  finish,
end

variables {G : Type*} [comm_group G] [fintype G]

instance : fintype (subgroup G) := fintype.of_injective (coe : subgroup G → set G) $ λ _ _, subgroup.ext'

/-
If a is a subgroup of G[2] and x ∈ G[2], then a ∪ x *l a is a subgroup.
-/
def insert_twotors_to_twotors {x : G} {a : subgroup G}
  (hx : x * x = 1) (ha : ∀ g : G, g ∈ a → g * g = 1) : subgroup G :=
{
  carrier := ↑a ∪ left_coset x a,
  one_mem' := or.inl (subgroup.one_mem a),
  mul_mem' := 
  begin
    intros u v hu hv,
    --rcases? hu hv,-- with ⟨ hu1, hu2⟩ | ⟨  hv1, hv2⟩ ,
    cases hv with hv1 hv2,
    repeat {cases hu with hu1 hu2},
    {
      exact or.inl (subgroup.mul_mem a hu1 hv1),
    },
    {
      right,
      rw [mem_left_coset_iff, ←mul_assoc],
      rw mem_left_coset_iff at hu2,
      exact is_submonoid.mul_mem hu2 hv1,
    },
    {
      right,
      rw [mul_comm, mem_left_coset_iff, ←mul_assoc],
      rw mem_left_coset_iff at hv2,
      exact is_submonoid.mul_mem hv2 hu1,
    },
    {
      left,
      rw mem_left_coset_iff at hu2 hv2,
      have H : x⁻¹ * x⁻¹ * u * v ∈ a,
      {
          norm_cast at hu2 hv2 ⊢,
          rw [mul_comm, mul_assoc, ←mul_assoc v _, mul_comm v _],
          exact subgroup.mul_mem a hv2 hu2,
      },
      have x_eq_xinv : x = x⁻¹ := eq_inv_of_mul_eq_one hx,
      rw [←x_eq_xinv, hx, one_mul] at H,
      exact H,
    }
  end,
  inv_mem' := 
  begin
      intros u hu,
      cases hu with hu1 hu2, by exact or.inl (is_subgroup.inv_mem hu1),
      {
          right,
          rw mem_left_coset_iff at hu2 ⊢,
          norm_cast at hu2 ⊢,
          rw [←subgroup.inv_mem_iff, mul_inv, inv_inv, inv_inv],
          have x_eq_xinv : x = x⁻¹ := eq_inv_of_mul_eq_one hx,
          rw ←x_eq_xinv at hu2,
          exact hu2,
      }
  end
}
/--
If g ∈ G[2] and a ≤ G[2], then a ∪ g l* a ⊆ G[2].
--/
lemma twotorsion_contains_a_and_ga {g : G} {a : subgroup G}
  (h₁ : g * g = 1) (h₂ : ∀ (x : G), x ∈ a → x * x = 1) :
    ↑a ∪ left_coset g ↑a ⊆ {x : G | x * x = 1} :=
begin
  -- prove that twotorsion(G) ⊇ a u ga 
  intros x hx,
  by_cases (x ∈ a), tauto,
  have H : (x ∈ left_coset g a),
  {
      rw set.mem_union at hx,
      norm_cast at hx,
      tauto,
  },
  suffices x_is_twotors : x * x = 1, by tauto,
  clear hx h,
  have H2 : ∀ (x : G), x ∈ a → x * x = 1, by tauto,
  rw mem_left_coset_iff at H,
  specialize H2  (g⁻¹ * x) H,
  have H3 : g = g⁻¹ := eq_inv_of_mul_eq_one h₁,
  by calc
  x * x = g * g * x * x : by simp only [h₁, one_mul]
  ...   = g⁻¹ * g⁻¹ * x * x : by rw ← H3
  ...   = g⁻¹ * x * g⁻¹ * x : by rw mul_right_comm g⁻¹ g⁻¹ x
  ...   = g⁻¹ * x * (g⁻¹ * x) : by exact mul_assoc (g⁻¹ * x) g⁻¹ x
  ...   = 1 : by exact H2,
end

/--
Suppose a ≤ G[2], and g ∉ a.
Then if x ∈ G[2] and x ∉ g l* a,
then g ∉ ⟨ x, a ⟩.
--/
lemma g_notin_xua {x g: G} {a : subgroup G}
  (hg : g ∉ a)
  (hx : x * x = 1)
  (ha : ∀ y : G, y ∈ a → y * y = 1)
  (hgx : x ∉ left_coset g ↑a) :
    (g ∉ insert_twotors_to_twotors hx ha) :=
begin
  by_contradiction cont,
  cases cont,
  by contradiction,
  {
      rw mem_left_coset_iff at *,
      suffices : g⁻¹ * x ∈ ↑a, by solve_by_elim,
      norm_cast at *,
      rw [←subgroup.inv_mem_iff, mul_inv, mul_comm, inv_inv],
      exact cont,
  }
end

/--
If x ∈ G[2] and a ≤ G[2], then ⟨ x, a ⟩ ≤ G[2].
--/
lemma xua_twotors {x : G} {a : subgroup G}
  (hx : x * x = 1)
  (ha : ∀ y : G, y ∈ a → y * y = 1) :
    (∀ (y : G), y ∈ (insert_twotors_to_twotors hx ha) → y * y = 1) :=
begin
  intros y hy,
  let xua := insert_twotors_to_twotors hx ha,
  have hxinxua : ∀ y : G, y ∈ xua ↔ (y ∈ ↑a ∨ y ∈ left_coset x a), by apply subgroup.mem_coe,
  rw hxinxua at hy,
  cases hy, by exact ha y (subgroup.mem_coe.mp hy),
  {
    rw mem_left_coset_iff at hy,
    have HH : ∃ w ∈ a, x⁻¹ * y = w, by tauto,
    rcases HH with ⟨ w ,⟨ hw1, hw2⟩⟩,
    have hhy : y = x * w := eq_mul_of_inv_mul_eq hw2,
    calc
    y * y = (x * w) * (x * w): congr (congr_arg has_mul.mul hhy) hhy
    ...   = (x * x) * (w * w): mul_mul_mul_comm x w x w
    ...   = w * w : mul_left_eq_self.mpr hx
    ...   = 1      : ha w hw1,
  }
end

/--
G[2] ≤ ⟨g, a⟩
--/
lemma twotorsion_containedin_a_union_ga {g : G} {a : subgroup G}
      (h₁ : g * g = 1) (h₂ : ∀ (x : G), x ∈ a → x * x = 1)
      (hga : g ∉ a)
      (hmax : ∀ (a' : subgroup G), g ∉ a' → (∀ (x : G), x ∈ a' → x * x = 1) → a ≤ a' → a = a') :
      {x : G | x * x = 1} ⊆ ↑a ∪ left_coset g ↑a :=
begin
  -- Prove that twotorsion(G) ⊆ a u ga
  intros x hx,
  dsimp at hx,
  by_contradiction h,
  rw set.mem_union at h,
  push_neg at h,
  let xua := insert_twotors_to_twotors hx h₂,
  have hxinxua : ∀ y : G, y ∈ xua ↔ (y ∈ ↑a ∨ y ∈ left_coset x a), by apply subgroup.mem_coe,
  have g_notin_xua : g ∉ xua, by exact g_notin_xua hga hx h₂ h.right,
  have h_twotors : (∀ (y : G), y ∈ xua → y * y = 1), by exact xua_twotors hx h₂,
  have a_eq_xua : a = xua := hmax xua g_notin_xua h_twotors (λ y hy, or.inl hy),
  have x_in_a : x ∈ a,
  {
      norm_cast at *,
      rw [a_eq_xua, hxinxua, mem_left_coset_iff],
      right,
      simp only [subgroup.mem_coe, mul_left_inv],
      exact subgroup.one_mem a
  },
  norm_cast at h,
  have hl := h.left,
  trivial,
end

-- given G two torsion and 1 ≠ g ∈ G, there is H < G of index 2 with g ∉ H
lemma element_avoidance {g : G}  (h₁ : g ≠ 1) (h₂ : g * g = 1):
 ∃ (H : subgroup G) ,
  (g ∉ H ∧ 
  (∀ (x : G), x ∈ H → x * x = 1) ∧ 
  {x : G | x * x = 1} = H ∪ (left_coset g H)) 
  :=
begin
    let s := {X : subgroup G | g ∉ X ∧ (∀ x : G, x ∈ X → x*x = 1)},
    have sfin : s.finite := set.finite.of_fintype _,
    have snonempty : set.nonempty s,
    {
        use ⊥,
        split,
        exact h₁,
        intros x hx,
        rw subgroup.mem_bot at hx,
        rw hx,
        exact mul_one 1,
    },
    let existsH := set.finite.exists_maximal_wrt id s sfin snonempty,
    simp only [and_imp, exists_prop, id.def, set.mem_set_of_eq] at existsH,
    cases existsH with a ha,
    use a,
    repeat {split},
    exact ha.1.1,
    exact ha.1.2,
    -- We have defined a as the maximal subgroup of G satisfying
    -- 1) g ∉ a
    -- 2) ∀ x ∈ a, x*x = 1
    -- Now we must show that a ∪ ga = twotorsion(G)
    apply set.subset.antisymm,
    apply twotorsion_containedin_a_union_ga h₂ ha.1.2 ha.1.1 ha.2,
    exact twotorsion_contains_a_and_ga h₂ ha.1.2,
end

lemma disjoint_cosets {g : G} {a : subgroup G} (hga : g ∉ a) : disjoint ↑a (left_coset g ↑a) :=
begin
    rintros x ⟨ h1, ⟨ w ,⟨ hw1, hw2⟩⟩⟩,
    suffices H : g ∈ a, by solve_by_elim,
    rw eq_mul_inv_of_mul_eq hw2,
    exact subgroup.mul_mem a h1 (subgroup.inv_mem a hw1),
end

lemma prod_square_eq_one {H : subgroup G} (h: ∀ (x : G), x ∈ H → x * x = 1) :
    (∏ (x : H), ↑x) * (∏ (x : H), ↑x) = (1 : G) :=
begin
    rw ←finset.prod_mul_distrib,
    norm_cast at *,
    simp,
    have h' : (∏ x : H, (1 : G)) = (1:G) := fintype.prod_eq_one (λ (a : ↥H), 1) (congr_fun rfl),
    rw_mod_cast ←h',
    clear h',
    apply finset.prod_congr, refl,
    intros x hx,
    specialize h x,
    apply h,
    cases x,
    assumption
end

lemma prod_square_eq_one' {H : subgroup G} (h: ∀ (x : G), x ∈ H → x * x = 1) :
    (∏ (x : G) in (H : set G).to_finset, x) * (∏ (x : G) in (H : set G).to_finset, x) = (1 : G) :=
begin
    rw ←two_products_id,
    apply prod_square_eq_one h,
    finish,
end

lemma fintype_card_eq_finset_card : fintype.card G =
       finset.card (((⊤ : subgroup G) : set G).to_finset):=
begin
    unfold fintype.card,
    congr,
    rw subgroup.coe_top,
    convert set.to_finset_univ.symm,
end

lemma prod_over_left_coset {g : G} {H : subgroup G} :
    ∏ x in (left_coset g ↑H).to_finset, x  = 
    g^(finset.card (H : set G).to_finset) * (∏ x in (H : set G).to_finset, x) :=
begin
    have h : ∏ x in (left_coset g ↑H).to_finset, x  = ∏ x in (H : set G).to_finset, (g * x),
    {
        unfold left_coset,
        --λ x : G, g * x,
        simp [finset.prod_image],
        unfold_coes,

        have hinj : ∀ (x : G), x ∈ (H : set G).to_finset → ∀ (y : G), y ∈ (H : set G).to_finset → g * x = g * y → x = y,
        {
            intros x hx y hy hg,
            exact (mul_right_inj g).mp hg,
        },
        convert finset.prod_image hinj,
        ext1,
        norm_num,
        split; tauto,
    },
    rw [h, finset.prod_mul_distrib],
    simp only [finset.prod_const],
end

lemma prod_identity {g : G} (h₁ : ∀ x : G, x * x = 1) (h₂ : g ≠ 1):
 ((∏ x : G, x) : G)= g^(fintype.card G / 2 : ℕ) :=
begin
    rw_mod_cast prod_all_eq_prod_two_torsion',
    have existsH := element_avoidance h₂ (h₁ g),
    rcases existsH with ⟨H, ⟨ hgH, hHtors, h_index2⟩⟩,
    have hdisj : disjoint (H : set G) (left_coset g ↑H) := disjoint_cosets hgH,
    have hdisj' : disjoint (H : set G).to_finset (left_coset g ↑H).to_finset,
    {
        intros x hx,
        simp only [finset.inf_eq_inter, subgroup.mem_coe, set.mem_to_finset, finset.mem_inter] at hx,
        apply hdisj hx,
    },
    have all_twotors : (two_torsion_subgroup G) = ⊤,
    {
        unfold two_torsion_subgroup,
        ext1,
        tauto,
    },
    have dec : ∀ x : G, x ∈ ((H : set G) ∪ left_coset g ↑H),
    {
        intro x,
        specialize h₁ x,
        rw ←h_index2,
        assumption,
    },
    have dec' : (H : set G).to_finset ∪ ((left_coset g ↑H).to_finset) = ((⊤ : subgroup G) : set G).to_finset,
    {
        ext1,
        split;
        finish,
    },
    have p2 : ((∏ (x : G) in (two_torsion_subgroup G : set G).to_finset, x) : G) = ((∏ x in (↑H : set G).to_finset, x) : G) * (∏ x in (left_coset g ↑H).to_finset, x ),
    {
        convert finset.prod_union hdisj',
        rw dec',
        congr,
        exact all_twotors,
    },
    have p3 : fintype.card G = 2 * finset.card (H : set G).to_finset,
    {
        have h' : finset.card (H : set G).to_finset = finset.card (left_coset g H).to_finset,
        {
            clear hdisj hdisj' p2 h₁ h₂ hHtors all_twotors,
            have hinj : function.injective (λ (x : G), g*x),
            {
                unfold function.injective,
                intros x y hxy,
                exact (mul_right_inj g).mp hxy,
            },
            rw ←finset.card_image_of_injective ((H : set G).to_finset) hinj,
            congr,
            ext,
            finish,
        },
        suffices h1 : fintype.card G = finset.card (H : set G).to_finset + finset.card (left_coset g H).to_finset, by linarith,
        have h2 : finset.card ((H : set G).to_finset ∪ (left_coset g H).to_finset)
            = finset.card (H : set G).to_finset + finset.card (left_coset g H).to_finset, by apply finset.card_disjoint_union hdisj',
        rw ←h2,
        convert fintype_card_eq_finset_card,
    },
    have p3' : fintype.card G / 2 = finset.card (H : set G).to_finset, by finish,
    rw [p3', p2, prod_over_left_coset, mul_comm, mul_assoc, mul_right_eq_self],
    suffices p4 : (∏ (x : G) in (H : set G).to_finset, x) * (∏ (x : G) in (H : set G).to_finset, x) = (1 : G), by assumption,
    solve_by_elim,
end

theorem two_torsion_subgroup_idem (G : Type*) [comm_group G] :
  two_torsion_subgroup (two_torsion_subgroup G) = ⊤ :=
begin
    apply eq_top_iff.2,
    intros x hx,
    apply subtype.eq,
    apply x.2,
end

instance subgroup.coe_is_monoid_hom {G : Type*} [group G] (H : subgroup G) :
    is_monoid_hom (coe : H → G) := by refine {..}; intros; refl


lemma prod_identity_general' {g : two_torsion_subgroup G} (h : g ≠ 1):
 (∏ x : G, x) = g^(fintype.card (two_torsion_subgroup G) / 2) :=
 begin
    have h1: (g : G) ≠ 1,
    {
        cases g,
        finish,
    },
    rw prod_all_eq_prod_two_torsion,
    let G2 := two_torsion_subgroup G,
    have htors : ∀ (x : G2),  x * x = 1,
    {
        intro x,
        rw ←mem_two_torsion_iff_square_eq_one,
        rw two_torsion_subgroup_idem,
        solve_by_elim,
    },
    norm_cast,
    rw ←prod_identity htors h,
    apply finset.prod_hom,
end

theorem prod_identity_general {g : G} (h1 : g ≠ 1) (h2 : g * g = 1) :
 (∏ x : G, x) = g^(fintype.card (two_torsion_subgroup G) / 2) :=
 begin
    suffices hg : (⟨ g, h2⟩  : two_torsion_subgroup G) ≠ 1, by exact prod_identity_general' hg,
    intro h, injections_and_clear, tauto,
 end

