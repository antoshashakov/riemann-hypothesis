module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLead
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalLeadingForm
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.dual_stacked_exceptional_leading_form : GroundTheory.Heights₂.Heights.DualStackedExcLeadForm.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm | exact GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm <;> assumption)
