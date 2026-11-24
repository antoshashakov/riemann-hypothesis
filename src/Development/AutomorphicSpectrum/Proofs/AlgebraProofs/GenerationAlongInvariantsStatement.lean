module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenerationAlongInvariants
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.generation_along_invariants : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun | exact GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun <;> assumption)
