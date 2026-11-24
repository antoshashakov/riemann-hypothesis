module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLatticeIsoAndTermsAgree
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaRecognition_lattice_iso_and_terms_agree : AllMatch fun μ _ _ => μ.A → ∃ e, μ.B e ∧ μ.Term e := by
  first | exact @GlobalTheory.MatchTerm.main | exact GlobalTheory.MatchTerm.main | (intros; apply GlobalTheory.MatchTerm.main <;> assumption)
