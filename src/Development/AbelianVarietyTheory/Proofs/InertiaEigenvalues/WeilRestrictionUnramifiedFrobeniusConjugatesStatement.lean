module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRestrictionUnramifiedFrobeniusConjugates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.weilRestriction_unramified_frobeniusConjugates : WeilRes := by
  first | exact @GlobalTheory.PMon.weilRes | exact GlobalTheory.PMon.weilRes | (intros; apply GlobalTheory.PMon.weilRes <;> assumption)
