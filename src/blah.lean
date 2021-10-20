import group_theory.subgroup
import group_theory.coset
import data.fintype.card
import data.set.finite
import data.zmod.basic
import basic
import tactic

open_locale classical big_operators
noncomputable theory

-- set_option profiler true

variables {p r n : ℕ} [fact p.prime] [1 ≤ r]

def R := units( zmod n)

def C2 (m : ℕ) : subgroup (units (zmod m)) :=
{ carrier := {1, -1},
  one_mem' := set.mem_insert 1 {-1},
  mul_mem' := λ a b (ha : a ∈ {1, -1}) (hb : b ∈ {1, -1}), by finish,
  inv_mem' := λ a (ha : a ∈ {1, -1}), by finish }

instance is_fintype (m : ℕ) : fintype (C2 m) := fintype (C2 m) := set.fintype_insert 1 {-1}

lemma card_C2_is_two (m : ℕ) (h: 2 < m) : fintype.card (C2 m) = 2 :=
begin
sorry
end

instance tr : fact (0 < p^r) :=
begin
    have h1 : 0 < p := nat.prime.pos _inst_1,
    apply nat.pos_pow_of_pos,
    exact h1,
end


lemma two_torsion_subgroup_of_primepow : two_torsion_subgroup (units (zmod (p^r))) = C2 (p^r) :=
begin
ext1 x,
fconstructor,
{
    intro hx,
    change x * x = 1 at hx,
    by_contradiction,
    sorry
},
{
    intro hx,
    ext1,
    cases hx; finish,
}
end




