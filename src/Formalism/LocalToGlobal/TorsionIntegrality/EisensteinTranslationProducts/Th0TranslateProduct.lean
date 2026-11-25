module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroTranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.EvenThetaSecond
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ThetaFunctionQuasiPeriodic
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.L2.Th1.F

theorem opUTh0 : OpUTh0 := operator_u_theta
theorem th0Line : ThetaZeroLine := even_theta_line

end Formalism.L2.Th1.F
