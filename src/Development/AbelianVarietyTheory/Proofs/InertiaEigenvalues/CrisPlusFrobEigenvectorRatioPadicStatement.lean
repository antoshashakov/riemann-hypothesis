module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrisPlusFrobEigenvectorRatioPadic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.crisPlus_frob_eigenvector_ratio_padic : Ratio := by
  first | exact @GlobalTheory.PMon.ratio_holds | exact GlobalTheory.PMon.ratio_holds | (intros; apply GlobalTheory.PMon.ratio_holds <;> assumption)
