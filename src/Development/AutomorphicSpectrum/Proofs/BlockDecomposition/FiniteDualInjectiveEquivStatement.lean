module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDualInjectiveEquiv
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Statement
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.finite_dual_injective_equiv : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y], (∃ f : Y →ₗ[ZMod n] Module.Dual (ZMod n) X, Function.Injective f) → (∃ g : X →ₗ[ZMod n] Module.Dual (ZMod n) Y, Function.Injective g) → Nonempty (Y ≃ₗ[ZMod n] Module.Dual (ZMod n) X) ∧ Nat.card X = Nat.card Y := by
  first | exact @GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair | exact GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair | (intros; apply GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair <;> assumption)
