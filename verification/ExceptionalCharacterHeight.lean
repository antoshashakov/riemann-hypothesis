import ConductorOneCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.TorsClass

/-!
# Trivial-character cohomology at the exceptional odd primes

Principia's collaborative RH project found this specialization of Levent
Alpöge's `zOne`. At 3 the whole Case IV summand vanishes on a principal
host. At 7 the same argument applies whenever 3 divides the twist.
-/

namespace Principia.Ordinary.ExceptionalCharacters

open NumberField Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/-- The prime-to-index restriction theorem applies at every odd prime of a principal host. -/
theorem odd_not_dvd_index (h : Host) (one : h.chi = PChar.one) {l : ℕ}
    (prime : l.Prime) (odd : l ≠ 2) : ¬ l ∣ h.H.index := by
  have index := (hostIndex h).1
  have order : h.o = 1 := by change ordC h.chi = 1; rw [one]; exact orderOf_one
  rw [order, mul_one] at index
  exact fun d => odd ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp
    (prime.dvd_of_dvd_pow (d.trans index)))

variable (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

theorem trivial_zero (h : Host) (l : ℕ) [Fact l.Prime] (c : Coef l)
    (odd : l ≠ 2) (e : ℕ) (positive : 1 ≤ e) (divides : l - 1 ∣ e) :
    Vlen Ω c e (1 : DirichletCharacter c.O h.N) = 0 := by
  have hg : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O h.N) = 1 := by
    ext σ
    simp [Chr.dirG]
  unfold Vlen
  rw [hg]
  exact le_antisymm ((Chr.V'_le_V l h.N e 1).trans
    (UpperTheory.V.X.zOne Ω l c.O odd e positive divides).le) bot_le

private theorem trivial_parity (h : Host) (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ)
    (mem : (1 : DirichletCharacter c.O h.N) ∈ h.X c e) : Even e := by
  have hv := (h.mem_X.1 mem).2
  unfold PsiEven at hv
  rw [MulChar.one_apply (isUnit_one.neg)] at hv
  by_contra he
  rw [(Nat.not_even_iff_odd.mp he).neg_one_pow] at hv
  have bad : (2 : c.O) = 0 := by linear_combination hv
  exact two_ne_zero bad

theorem caseIV_zero_of_dvd (h : Host) (one : h.chi = PChar.one)
    {t l e : ℕ} [Fact l.Prime] (c : Coef l) (big : h.Big t) (odd : l ≠ 2)
    (ψ : DirichletCharacter c.O h.N) (mem : ψ ∈ h.X c e) (civ : h.CaseIV l e ψ)
    (divides : Even e → l - 1 ∣ e) : Vlen Ω c e ψ = 0 := by
  obtain ⟨_, he, rfl⟩ := (CharacterCases.exceptional_caseIV_iff one
    (h.mem_X.1 mem).1 big Fact.out odd).mp civ
  exact trivial_zero Ω h l c odd e (by omega) (divides (trivial_parity h l c e mem))

theorem caseIV_three (h : Host) (one : h.chi = PChar.one) {t e : ℕ}
    (c : Coef 3) (big : h.Big t) (ψ : DirichletCharacter c.O h.N)
    (mem : ψ ∈ h.X c e) (civ : h.CaseIV 3 e ψ) : Vlen Ω c e ψ = 0 :=
  caseIV_zero_of_dvd Ω h one c big (by decide : 3 ≠ 2) ψ mem civ fun even => by
    simpa only [Nat.reduceSub] using even.two_dvd

local instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

theorem caseIV_seven (h : Host) (one : h.chi = PChar.one) {t e : ℕ}
    (c : Coef 7) (big : h.Big t) (ψ : DirichletCharacter c.O h.N)
    (mem : ψ ∈ h.X c e) (civ : h.CaseIV 7 e ψ) (div3 : 3 ∣ e) : Vlen Ω c e ψ = 0 :=
  caseIV_zero_of_dvd Ω h one c big (by decide : 7 ≠ 2) ψ mem civ fun even => by
    have d2 := even.two_dvd
    omega

end Principia.Ordinary.ExceptionalCharacters

#print axioms Principia.Ordinary.ExceptionalCharacters.odd_not_dvd_index
#print axioms Principia.Ordinary.ExceptionalCharacters.trivial_zero
#print axioms Principia.Ordinary.ExceptionalCharacters.caseIV_three
#print axioms Principia.Ordinary.ExceptionalCharacters.caseIV_seven
