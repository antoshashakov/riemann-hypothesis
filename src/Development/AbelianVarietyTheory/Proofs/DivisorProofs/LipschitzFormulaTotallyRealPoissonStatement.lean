module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoisson
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.lipschitz_formula_totally_real_poisson : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz := by
  first | exact @GlobalTheory.LipschitzTR.lipschitz | exact GlobalTheory.LipschitzTR.lipschitz | (intros; apply GlobalTheory.LipschitzTR.lipschitz <;> assumption)
