module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLead
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedGraphBihomogeneous
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.dual_stacked_graph_bihomogeneous : GroundTheory.Heights₂.Heights.DualStackedGraphBihomog.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog | exact GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog <;> assumption)
