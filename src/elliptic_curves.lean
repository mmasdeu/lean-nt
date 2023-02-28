import divpolys


noncomputable theory
open_locale classical

open polynomial
open nat

variables {R : Type*} [field R] -- should work with comm_ring but some lemmas used for simp won't work
variables (A B : R)

local notation `ψ'` := psi' A B
local notation `ψ2` := psisq A B
local notation `φ` := phi A B
local notation `ω'` := omega' A B
local notation `ω2` := omega_sq A B 

-- Prove that Pn + Pn = P2n

-- This has been checked by Sage for n = 2 and 3
lemma phi_bit0 {n : ℕ} (hn : 2 ≤ n)
(hc : (ω2 n * (ite (even n) 1 (4 * (X ^ 3 + A • X + B • 1)))) = φ n^3 + A • φ n * ψ2 n ^ 2 + B • ψ2 n ^ 3 ) :
 φ (2*n) = (φ n)^4  - 2 * A • (φ n)^2 * (ψ2 n)^2 - 8 * B•(φ n)*(ψ2 n)^3 + A^2•(ψ2 n)^4 :=
begin
  unfold phi,
  have ht : even (2*n) := sorry,
  by_cases he : even n,
  {
    simp [he, ht] at hc ⊢,
    rw psisq_bit0_even A B hn he hc,
    rw psi_bit1 _ _ (le_of_succ_le hn),
    rw psi_bit1' _ _ hn,
    simp [he],
    rw ←hc,
    rw psisq_def _ _ he,
    rw omega_sq_def,
    rw omega'_def,
    simp [he, ht],
    
    sorry
  },
  {
    sorry
  }
end
/- 
-- This proves that x(2P) is given by the corresponding division polynomials
lemma main_theorem (n : ℕ) :
(ω' n * (ite (even n) 1 (4 * (X ^ 3 + A • X + B • 1))))^2 =
 φ n^3 + A • φ n * ψ2 n ^ 2 + B • ψ2 n ^ 3 ∧ 
  φ(2*n) * 4 * ψ2 n * ((φ n)^3 + A • φ n * (ψ2 n)^2 + B • (ψ2 n)^3)
   = (ψ2 (2*n)) * ((φ n)^4 - 2*A•(φ n)^2*(ψ2 n)^2 - 8*B•(φ n)*(ψ2 n)^3 + A^2•(ψ2 n)^4) :=
begin
  apply induction_ppl_bit n,
  { split;
    simp [omega', psi', phi, psisq] },
  {
    intros m hm,
    obtain ⟨hm1, hm2⟩ := hm,
    have hemt : even (2 * m) := even.mul_left (nat.even_bit0 1) _,
    simp [hemt],
    split,
    {
      sorry
    },
    {
      by_cases hm0 : 2 ≤ 2 * m,
      {
        rw phi_bit0 _ _ hm0 hm1,
      },
      {
        -- should be easy
        sorry
      }
      
    }
  },
  {
    sorry
  }
end
 -/
/- begin
    simp [psisq_bit0 A B hn, phi_bit0 A B hn],
    ring,
    /- 
    apply induction_ppl,
    {
      unfold psi',
      simp [psi', psisq],
      ring_poly,
    },
    intros n hn H,
    have two_leq_n : 2 ≤ n,
    { sorry },
    have two_leq_np1 : 2 ≤ n+1,
    { sorry },
    have htwon : even (2*n),
    {sorry},
    have htwon' : ¬ even (2*n+1),
    {sorry},
    have htwon'' : even (2*(n+1)),
    {sorry},
    have htwon''' : ¬ even (2*(n+1)+1),
    {sorry},
    simp [htwon, htwon', htwon'',htwon'''] at H ⊢,
    by_cases hev : even n,
    {
      have hev' : ¬ even (n+1),
      {sorry},
      unfold psisq,
      simp [hev, htwon, htwon', htwon'', htwon''', hev', psisq, psi'] at H ⊢,
      rw psi_bit0 _ _ two_leq_n at H,
      rw psi_bit0 _ _ two_leq_np1,
      rw psi_bit1 _ _ two_leq_np1,
      simp [hev, htwon, htwon', htwon'', htwon''', hev', psisq, psi', psi_simp] at ⊢,
      rw psi_bit1 _ _ two_leq_n,
      simp [hev, htwon, htwon', htwon'', htwon''', hev', psisq, psi'] at ⊢,
      simp only [psi_simp'],
      simp only [psi_simp''],
      simp only [psi_simp'],
      generalize hn : psi' A B (n-1) = xn,
      generalize hn0 : psi' A B n = xn0,
      generalize hn1 : psi' A B (n+1) = xn1,
      generalize hn2 : psi' A B (n+2) = xn2,
      generalize hn3 : psi' A B (n+3) = xn3,
      apply polynomial.eq_of_subs,
      simp,
      --simp only [psi_simp, psi_simp', psi_simp''],


      --norm_num,
      
      sorry
    },
    {
      have hev' : even (n+1),
      {sorry},
      simp [psi', psisq],
      sorry
    } -/
end
 -/


/- example (n : ℕ) (h : n = 2): 
φ(2*n) * 4 * ψ2 n * ((φ n)^3 + A • φ n * (ψ2 n)^2 + B • (ψ2 n)^3)
   = (ψ2 (2*n)) * ((φ n)^4 - 2*A•(φ n)^2*(ψ2 n)^2 - 8*B•(φ n)*(ψ2 n)^3 + A^2•(ψ2 n)^4) :=
begin
  subst h,
  have h4e : even (2*2) := sorry,
  have h1 : 2 * 2 = 4 := sorry,
  have h2 : 2 * 2 + 1 = 5 := sorry,
  simp [phi, psi', psisq, h4e, h1, h2],
  apply polynomial.eq_of_subs,
  intro r,
  simp,
  ring,
end
 -/
/- example (n : ℕ) (h : n = 3): 
φ(2*n) * 4 * ψ2 n * ((φ n)^3 + A • φ n * (ψ2 n)^2 + B • (ψ2 n)^3)
   = (ψ2 (2*n)) * ((φ n)^4 - 2*A•(φ n)^2*(ψ2 n)^2 - 8*B•(φ n)*(ψ2 n)^3 + A^2•(ψ2 n)^4) :=
begin
  subst h,
  have h4e : even (2*2) := sorry,
  have h1 : 2 * 3 = 6 := sorry,
  have h2 : 2 * 3 + 1 = 7 := sorry,
  simp [phi, psi', psisq, h4e, h1, h2],
  apply polynomial.eq_of_subs,
  intro r,
  simp,
  -- SAGE checks it!
  sorry
  --ring_exp,
  --ring_poly,
end
 -/

--R.<A,B> = PolynomialRing(QQ)
-- E = EllipticCurve([A,B])
-- x = E.division_polynomial_0(2).parent().gen()
--psip = lambda n : (E.division_polynomial_0(n) if n > 0 else 0)
--psisq = lambda n : psip(n)**2 * ( (4 * (x^3+A*x+B)) if n % 2 == 0 else 1)
--omega = lambda n : psip(n+2) *psip(n-1)**2 - psip(n-2)*psip(n+1)**2
-- phi = lambda n : x * psisq(n) - psip(n+1)*psip(n-1)*(1 if n % 2 == 0 else (4*(x^3+A*x+B)))

-- n = 2
-- pn = phi(n)
-- dn = psisq(n)
-- LHS = (pn^4 - phi(2*n)) // psisq(n)^2
-- RHS = (2*A*pn^2*dn^2 + 8*B*pn*dn^3 - A^2 *dn^4) // psisq(n)^2
-- Can show: Res(x^4-2*A*x^2-8*B*x+A^2, x^3+A*x+B) = (4*A^3+27*B^2)^2
--  