module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsInvStabilizerCardMass
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.finsum_orbits_inv_stabilizer_card_mass : ∀ {K Z : Type} [Group K] [Finite K] [MulAction K Z] (f : Z → ℂ), (∀ (k : K) (z : Z), f (k • z) = f z) → (Function.support f).Finite → ∑ᶠ o : MulAction.orbitRel.Quotient K Z, ((Nat.card (MulAction.stabilizer K (Quotient.out o)) : ℕ) : ℂ)⁻¹ * f (Quotient.out o) = ((Nat.card K : ℕ) : ℂ)⁻¹ * ∑ᶠ z, f z := by
  first | exact @GlobalTheory.finsum_orbits_stabilizer_mass | exact GlobalTheory.finsum_orbits_stabilizer_mass | (intros; apply GlobalTheory.finsum_orbits_stabilizer_mass <;> assumption)
