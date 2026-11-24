module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfFrobeniusUnitEigenvectorGaloisLine
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.ainf_frobenius_unit_eigenvector_galois_line : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l) (u : ℤ_[l]ˣ), IsUnit w → Per.φA l w = Per.zA l u * w → ∀ g : GQ l, ∃ z : ℤ_[l], Per.σB g (Per.aB l w) = Per.zB l z * Per.aB l w := by
  first | exact @GlobalTheory.UnitLine.sigma_unit_eigen | exact GlobalTheory.UnitLine.sigma_unit_eigen | (intros; apply GlobalTheory.UnitLine.sigma_unit_eigen <;> assumption)
