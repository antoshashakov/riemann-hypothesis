module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.locally_free_finite_projective_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), LocFree R r L.toAddSubgroup → Module.Finite R L ∧ Module.Projective R L ∧ Module.finrank Ω E = r ∧ IsBaseChange Ω L.subtype := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main | exact GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main <;> assumption)
