module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.GaussDegenerate
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.UnitaryConstant
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyPhaseQuadratic
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.DifferentialRepresentation
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GapStatement
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaussSumEighthPower
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.SelfDualCovolumeProof
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.TripleEighthProof
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.UnitaryEighthOf
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.L2.Th1.H

theorem phiBasic : PhiBasic := cayleyPhaseBasic
theorem gaussEighth : GaussEighth := gaussSumEighthPower
theorem unitaryGauss : UnitaryGauss := UnitaryGauss_of gaussEighth
theorem detCayley : DetCayley := cayleyDet
theorem unitaryConstant : UnitaryConstant := UnitaryConstant_proof
theorem unitaryEighth : UnitaryEighth := UnitaryEighth_proof

theorem tripleFormula : TripleFormula := TripleFormula_proof
theorem psiQuadratic : PsiQuadratic := triplePhaseQuadratic
theorem tripleEighth : TripleEighth := TripleEighth_proof

end Formalism.L2.Th1.H
