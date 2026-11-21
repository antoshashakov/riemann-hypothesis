import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Cases

/-!
# Odd primes in the conductor-one height argument

This specialization of Levent Alpöge's character count was found through
Principia's collaborative Riemann Hypothesis project. A principal host has
character exponent dividing a power of two. Case III is empty, and Case IV
at an exceptional prime contributes only the trivial character.
-/

namespace Principia.Ordinary.CharacterCases

open Formalism.HC UpperTheory.Top UpperTheory.V UpperTheory.V.HV

private theorem principal_order (h : Host) (one : h.chi = PChar.one) : h.o = 1 := by
  change ordC h.chi = 1
  rw [one]
  exact orderOf_one

variable {O : Type} [CommRing O] [IsDomain O] {h : Host} {ψ : DirichletCharacter O h.N}

/-- The odd-order branch also disappears for every base character of 2-power order. -/
theorem trivial_of_odd_order {k : ℕ} (base : h.o ∣ 2 ^ k) (host : h.IsChar ψ)
    (odd : Odd (orderOf ψ)) : ψ = 1 := by
  have div : orderOf ψ ∣ 2 ^ (h.ex + 1 + k) := by
    rw [pow_add]
    exact (hostComp h O ψ host).1.trans (Nat.mul_dvd_mul_left _ base)
  have cop : (orderOf ψ).Coprime (2 ^ (h.ex + 1 + k)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr odd)
  have hd := Nat.dvd_gcd (dvd_refl (orderOf ψ)) div
  rwa [cop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hd

theorem no_caseIII_of_quadratic (square : h.chi.χ ^ 2 = 1) (host : h.IsChar ψ) (l e : ℕ) :
    ¬ h.CaseIII l e ψ := by
  have base : h.o ∣ 2 ^ 1 := by
    simp only [Host.o, ordC, pow_one]
    exact orderOf_dvd_of_pow_eq_one square
  exact fun caseIII => caseIII.2.2.2 (trivial_of_odd_order base host caseIII.2.2.1)

theorem order_dvd_two_power (one : h.chi = PChar.one) (host : h.IsChar ψ) :
    orderOf ψ ∣ 2 ^ (h.ex + 1) := by
  simpa only [principal_order h one, mul_one] using (hostComp h O ψ host).1

theorem odd_order_iff (one : h.chi = PChar.one) (host : h.IsChar ψ) :
    Odd (orderOf ψ) ↔ ψ = 1 := by
  refine ⟨fun odd => ?_, fun trivial => by simp [trivial]⟩
  exact trivial_of_odd_order (k := 0) (by simp only [principal_order h one, one_dvd]) host odd

theorem odd_prime_parts (one : h.chi = PChar.one) (host : h.IsChar ψ)
    {l : ℕ} (prime : l.Prime) (odd : l ≠ 2) : kap l ψ = 1 ∧ th0 l ψ = ψ := by
  have nd : ¬ l ∣ orderOf ψ := fun hdiv => odd
    ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp
      (prime.dvd_of_dvd_pow (hdiv.trans (order_dvd_two_power one host))))
  exact (partOrd _ l prime ψ (hostComp h O ψ host).2.1).2.2.2.2.2.1 nd

theorem no_caseIII (one : h.chi = PChar.one) (host : h.IsChar ψ) (l e : ℕ) :
    ¬ h.CaseIII l e ψ := fun c => c.2.2.2 ((odd_order_iff one host).mp c.2.2.1)

theorem exceptional_component (one : h.chi = PChar.one) (host : h.IsChar ψ)
    {t l : ℕ} (big : h.Big t) (prime : l.Prime) (odd : l ≠ 2) (exc : l ∈ Bchi h.chi) :
    chiP l ψ = ψ := by
  obtain ⟨hq, hd⟩ := (bchiFacts h t big).1 l exc
  have nd : ¬ l ∣ h.N := by
    intro d
    rcases ((hostIndex h).2.2.2.2.2.1 l prime).1 d with h2 | hq' | hq1 | hd'
    · exact odd h2
    · have hqone : h.q = 1 := by change h.chi.N = 1; rw [one]; rfl
      rw [hqone] at hq'
      exact prime.not_dvd_one hq'
    · omega
    · omega
  have atPrime := (hostComp h O ψ host).2.2 l prime odd
  simp only [chiP, (odd_prime_parts one host prime odd).2, atPrime.2.2.2 nd, inv_one, mul_one]

theorem exceptional_caseIV_iff (one : h.chi = PChar.one) (host : h.IsChar ψ)
    {t l e : ℕ} (big : h.Big t) (prime : l.Prime) (odd : l ≠ 2) :
    h.CaseIV l e ψ ↔ l ∈ Bchi h.chi ∧ 2 ≤ e ∧ ψ = 1 := by
  constructor
  · rintro ⟨exc, he, ho⟩
    rw [exceptional_component one host big prime odd exc] at ho
    exact ⟨exc, he, (odd_order_iff one host).mp ho⟩
  · rintro ⟨exc, he, trivial⟩
    refine ⟨exc, he, ?_⟩
    rw [exceptional_component one host big prime odd exc]
    exact (odd_order_iff one host).mpr trivial

theorem outside_cases (one : h.chi = PChar.one) (host : h.IsChar ψ)
    {t l e : ℕ} (big : h.Big t) (prime : l.Prime) (odd : l ≠ 2)
    (he : 0 < e) (ht : e < t) (outside : l ∉ Bchi h.chi) :
    h.CaseI l e ∨ h.CaseZ l e ψ ∨ h.CaseII l e ψ := by
  have choices := ((UpperTheory.V.HV.cases h t big O ψ host l e prime odd he ht).1 outside).2.2.2.2.2
  rcases choices with hi | hz | hii | hiii
  · exact Or.inl hi
  · exact Or.inr (Or.inl hz)
  · exact Or.inr (Or.inr hii)
  · exact (no_caseIII one host l e hiii).elim

end Principia.Ordinary.CharacterCases

#print axioms Principia.Ordinary.CharacterCases.order_dvd_two_power
#print axioms Principia.Ordinary.CharacterCases.trivial_of_odd_order
#print axioms Principia.Ordinary.CharacterCases.no_caseIII_of_quadratic
#print axioms Principia.Ordinary.CharacterCases.odd_prime_parts
#print axioms Principia.Ordinary.CharacterCases.no_caseIII
#print axioms Principia.Ordinary.CharacterCases.exceptional_caseIV_iff
#print axioms Principia.Ordinary.CharacterCases.outside_cases
