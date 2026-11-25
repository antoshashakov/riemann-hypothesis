module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLaws
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open CrystallineSemistableComparison.Onto

theorem _root_.GlobalTheory.T.onto_form_laws : CrystallineSemistableComparison.Onto.FormLaws := by
  first | exact @GlobalTheory.CompanionTheory.OntoForms.formLaws | exact GlobalTheory.CompanionTheory.OntoForms.formLaws | (intros; apply GlobalTheory.CompanionTheory.OntoForms.formLaws <;> assumption)
