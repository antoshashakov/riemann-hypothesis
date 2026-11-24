module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIndexOfIsOpenAbsGaloisFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.finiteIndex_of_isOpen_absGalois_finExt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (H : Subgroup ↥(GK K)), IsOpen (H : Set ↥(GK K)) → H.FiniteIndex := by
  first | exact @GlobalTheory.OpenFiniteIndex.finiteIndex_of_isOpen | exact GlobalTheory.OpenFiniteIndex.finiteIndex_of_isOpen | (intros; apply GlobalTheory.OpenFiniteIndex.finiteIndex_of_isOpen <;> assumption)
