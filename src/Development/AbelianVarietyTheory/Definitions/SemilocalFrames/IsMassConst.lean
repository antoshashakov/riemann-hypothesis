module

public import Mathlib.Data.Matrix.Diagonal
import Supplements.MathlibImports.AnalysisAndTactics
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

noncomputable section
open ValuativeRel IsDedekindDomain NumberField ComplexConjugate Formalism.MainNotions.S.Loc Matrix MeasureTheory
open scoped Classical

namespace GlobalTheory.SgGlob

section Rat
variable {E : Type} [Field E] [NumberField E]

def eps (K : Type) [CommRing K] (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal fun b => (-1) ^ (r - (b : ℕ))

end Rat

namespace ModFam
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {g₁ g₂ : ℕ} (X : ModFam F E sig g₁ g₂)

end ModFam

end GlobalTheory.SgGlob
