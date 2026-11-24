module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicMonodromyMatrixFormOfInductionCases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.padicMonodromyMatrixForm_of_induction_cases : FrameEx → TwistStep → SenStep → RedStep → ModStep → MatThm := by
  first | exact @GlobalTheory.PMon.matThm_of_steps | exact GlobalTheory.PMon.matThm_of_steps | (intros; apply GlobalTheory.PMon.matThm_of_steps <;> assumption)
