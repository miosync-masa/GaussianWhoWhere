import GaussianWhoWhere.ConcretePolynomials
import GaussianWhoWhere.PolynomialRigidity
import GaussianWhoWhere.LogMultiplicativity
import GaussianWhoWhere.FiniteUniqueness
import GaussianWhoWhere.FiniteGeneralUniqueness
import GaussianWhoWhere.HermitePochhammer
import GaussianWhoWhere.BridgeStructure
import GaussianWhoWhere.InfiniteCoupler
import GaussianWhoWhere.Infinite.FiniteExponentialType
import GaussianWhoWhere.Infinite.TranslationDefect
import GaussianWhoWhere.Infinite.ZeroDensityInterface
import GaussianWhoWhere.Infinite.ArithmeticSamples
import GaussianWhoWhere.Infinite.TwoShiftCoupler
import GaussianWhoWhere.Infinite.ExponentialSurvivorInterface
import GaussianWhoWhere.Infinite.WhereKillsExponential
import GaussianWhoWhere.Infinite.InfiniteRigidity
import GaussianWhoWhere.Infinite.LogSampleDensity
import GaussianWhoWhere.Infinite.WhereKillsExponentialConcrete
import GaussianWhoWhere.Infinite.TranslationZeros
import GaussianWhoWhere.Infinite.DensePeriodInterface
import GaussianWhoWhere.Infinite.DensePeriodCoupler
import GaussianWhoWhere.Infinite.LogDerivativeCoupler
import GaussianWhoWhere.Infinite.ExponentialSurvivorConcrete
import GaussianWhoWhere.Infinite.TranslationEigenLogDerivInterface
import GaussianWhoWhere.Infinite.LogDerivativeAlgebra
import GaussianWhoWhere.Infinite.TranslationEigenDeriv
import GaussianWhoWhere.Infinite.LogDerivativeContinuityInterface
import GaussianWhoWhere.Infinite.TranslationDefectToEigenCoupler
import GaussianWhoWhere.Infinite.SampledDefectToLogDerivConst
import GaussianWhoWhere.Infinite.TwoIncommensurableSampledLogDerivConst
import GaussianWhoWhere.Infinite.LogDerivativeContinuityConcrete
import GaussianWhoWhere.Infinite.LogDerivativeContinuityHolomorphic
import GaussianWhoWhere.Infinite.RealAxisConstToGlobalInterface
import GaussianWhoWhere.Infinite.GlobalLogDerivConstToExpInterface
import GaussianWhoWhere.Infinite.KroneckerDensity
import GaussianWhoWhere.Infinite.KroneckerPipeline
import GaussianWhoWhere.Infinite.WhereKillsExponentialFunctionLevel
import GaussianWhoWhere.Infinite.RealAxisConstToGlobalConcrete
import GaussianWhoWhere.Infinite.GlobalLogDerivConstToExpNormalized
import GaussianWhoWhere.Infinite.GlobalLogDerivConstToExpConcrete
import GaussianWhoWhere.Infinite.WhereKillsExponentialFunctionLevelConcrete
import GaussianWhoWhere.Infinite.ZeroCounting
import GaussianWhoWhere.Infinite.ZeroDensityForcesZeroRefined
import GaussianWhoWhere.Infinite.LogSampleZeroContradiction
import GaussianWhoWhere.Infinite.OddLogLinearZeroBoundBeating
import GaussianWhoWhere.Infinite.JensenCartwrightInterface
import GaussianWhoWhere.Infinite.JensenFinalPipeline
import GaussianWhoWhere.Infinite.FunctionalEquationFreezing
import GaussianWhoWhere.ZetaBridge.Basic
import GaussianWhoWhere.LFunctionBridge.Basic
import GaussianWhoWhere.LFunctionBridge.ZetaEulerProduct
import GaussianWhoWhere.LFunctionBridge.ZetaLogDerivative

/-!
# GaussianWhoWhere — theorem map

A single navigable index of the formalized results, organized by
level. Each `#check` below exposes the signature so that the IDE can
jump to the underlying definition.

## Formalized levels

* **Level 0** — Polynomial translation rigidity.
  A real polynomial `Q` with `Q(0) = 1` satisfying
  `Q(x + a) = Q(a) · Q(x)` for `a ≠ 0` is identically `1`.

* **Level 1 (abstract core)** — Sampled-translation rigidity.
  The rigidity already follows from the translation relation holding
  on a single injective sequence of sample points.

* **Level 2** — Finite Hermite–Pochhammer uniqueness.
  Inside the finite `P₄/P₈/P₁₂/P₁₆`-truncated deformation family,
  multiplicativity forces all deformation coefficients to vanish.

* **Level 2G** — *General* finite Hermite–Pochhammer uniqueness.
  For any finite truncation
  `Q_K(x) := 1 + Σ_{k=0}^{K-1} c_k · P_{4(k+1)}(x)`
  satisfying the Cauchy multiplicative equation, every `c_k = 0`.
  This generalizes Level 2 to arbitrary `K`. The proof uses the
  leading coefficient `(P2nPoly n).leadingCoeff = 2^(2n)` and
  descending induction on `K`.

* **Level 3** — Concrete polynomials and their Hermite–Pochhammer
  construction. The polynomials `P₄, P₈, P₁₂, P₁₆` carry reflection
  symmetry, are not additive, and are produced by the uniform
  Hermite–Pochhammer expansion `P_{2n}(s) = Σ h_j · 2^j · (s/2)_j`.

* **Level 4** — Who/Where bridge type structure.
  Type-level scaffolding for the who/where decomposition. No
  RH-strength implication is asserted here.

* **Infinite Coupler** — Bridge C skeleton.
  The infinite Hermite–Pochhammer extension is *not* analytically
  formalized here. Instead, the analytic inputs (HP_ft class,
  zero-density / two-translation exponential rigidity, where-kills-
  exponential) are abstracted as predicates / structures, and the
  pipeline `Who + Where ⇒ Q ≡ 1` is composed at the logical level.
-/

noncomputable section

namespace GaussianWhoWhere

/-! ## Level 0 -/

#check @polynomial_translation_rigidity

/-! ## Level 1 (abstract core) -/

#check @polynomial_translation_identity_of_infinite_eval
#check @polynomial_rigidity_of_infinite_sampled_translation

/-! ## Level 2 -/

#check @finite_concrete_uniqueness_P16
#check @finite_concrete_uniqueness_P16_of_translation
#check @Q4Poly_eq_one_of_translation
#check @coeffs_zero_of_Q4Poly_eq_one

/-! ## Level 2G — General finite Hermite–Pochhammer uniqueness -/

#check @coeff_P2nPoly_top
#check @natDegree_P2nPoly
#check @leadingCoeff_P2nPoly
#check @QFinitePoly
#check @QFinitePoly_eq_one_of_translation
#check @coeffs_zero_of_QFinitePoly_eq_one
#check @finite_general_uniqueness_of_translation
#check @finite_general_uniqueness

/-! ## Level 3 — concrete polynomials -/

#check @P4_symm
#check @P8_symm
#check @P12_symm
#check @P16_symm
#check @P4_not_additive
#check @P8_not_additive
#check @P12_not_additive
#check @P16_not_additive

/-! ## Level 3 — Hermite–Pochhammer generation (finite-coefficient layer) -/

#check @hermitePochhammer_H4_eq_P4
#check @hermitePochhammer_H8_eq_P8
#check @hermitePochhammer_H12_eq_P12
#check @hermitePochhammer_H16_eq_P16

/-! ## Level 3 — General `P_{2n}` construction (`P2nPoly`) -/

#check @halfX
#check @pochhammerHalfX
#check @eval_pochhammerHalfX
#check @hermiteEvenCoeff
#check @hermiteEvenCoeff_two_eq_H4Coeff
#check @hermiteEvenCoeff_four_eq_H8Coeff
#check @hermiteEvenCoeff_six_eq_H12Coeff
#check @hermiteEvenCoeff_eight_eq_H16Coeff
#check @P2nPoly
#check @P2nPoly_two_eval_eq_P4
#check @P2nPoly_four_eval_eq_P8
#check @P2nPoly_six_eval_eq_P12
#check @P2nPoly_eight_eval_eq_P16
#check @P2nPoly_two_symm
#check @P2nPoly_four_symm
#check @P2nPoly_six_symm
#check @P2nPoly_eight_symm
#check @P2nPolyReflectConjecture
#check @P2nPoly_recurrence_eval
#check @P2nPoly_reflect
#check @P2nPolyReflectConjecture_proved

/-! ## Level 1 — Concrete log-sample instantiation -/

#check @oddLogSample
#check @oddLogSample_injective
#check @polynomial_rigidity_of_odd_log_sampled_translation

/-! ## Level 4 — Who/Where bridge predicates -/

#check @ReflectedZeroSymmetry
#check @CriticalLineProperty
#check @FunctionalSymmetry
#check @ArithmeticIdentity
#check @WhoWhereCompatible
#check @where_gives_reflected_zero_geometry

/-! ## Infinite Coupler — Bridge C skeleton -/

#check @HPftLike
#check @InfiniteWho
#check @InfiniteWhere
#check @TwoTranslationExponentialRigidity
#check @WhereKillsExponential
#check @infinite_who_where_rigidity

/-! ## Infinite L3 — Finite exponential type (closure properties) -/

#check @FiniteExpType
#check @finiteExpType_const
#check @finiteExpType_translate
#check @finiteExpType_const_mul
#check @finiteExpType_add
#check @finiteExpType_sub

/-! ## Infinite L3 — Translation defect closure -/

#check @translationDefect
#check @finiteExpType_translationDefect
#check @realLogShiftDefect
#check @finiteExpType_realLogShiftDefect

/-! ## Infinite L3 — Zero-density interface -/

#check @SampledZeros
#check @ZeroDensityForcesZero
#check @AbstractDenseEnough
#check @zeroDensity_forces_zero
#check @translationDefect_eq_zero_of_sampledZeros
#check @translation_eigen_of_translationDefect_eq_zero
#check @translation_eigen_of_sampledZeros

/-! ## Infinite L3 — Arithmetic sampled who input -/

#check @SampledTranslationRelation
#check @sampledZeros_translationDefect_of_sampledTranslationRelation
#check @translation_eigen_of_sampledTranslationRelation
#check @SampledWhoInput
#check @SampledWhoInput.translation_eigen

/-! ## Infinite L3 — Two-shift coupler -/

#check @TwoSampledWhoInputs
#check @TwoSampledWhoInputs.translation_eigen₁
#check @TwoSampledWhoInputs.translation_eigen₂
#check @TwoGlobalTranslationEigen
#check @TwoSampledWhoInputs.toGlobalTranslationEigen
#check @TwoIncommensurableSampledWhoInputs
#check @TwoIncommensurableGlobalTranslationEigen
#check @TwoIncommensurableSampledWhoInputs.toGlobal

/-! ## Infinite L3 — Exponential survivor interface -/

#check @ExponentialSurvivor
#check @ExponentialSurvivorPrinciple
#check @exponential_survivor_of_two_global_translations
#check @exponential_survivor_of_two_sampled_who_inputs

/-! ## Infinite L3 — Where kills exponential (pipeline applications) -/

#check @one_of_where_and_exponential_survivor
#check @infinite_who_where_rigidity_from_sampled_inputs
#check @infinite_who_where_rigidity_from_global_translations

/-! ## Infinite L3 — Top-level infinite rigidity DAG -/

#check @infinite_rigidity_from_sampled_who_where
#check @infinite_rigidity_from_global_who_where
#check @bridgeC_infinite_coupler

/-! ## Infinite L3 — Log sample density (low-risk internalization) -/

#check @oddLogComplexSample
#check @oddLogComplexSample_injective
#check @odd_index_value_bound
#check @oddLogSample_monotone
#check @oddLogSample_le_of_index_lt
#check @finite_many_odd_log_samples
#check @log_sample_linear_lower_bound_interface

/-! ## Infinite L3 — Where kills exponential, concrete exponent-level core -/

#check @ExponentReflection
#check @exponentReflection_forces_zero
#check @ConcreteExponentialSurvivor
#check @whereKillsExponentLevel
#check @exponentReflection_of_linearExponentWhere

/-! ## Infinite L3 — Translation-eigen zero propagation -/

#check @zero_propagates_one_step
#check @zero_propagates_nat
#check @zero_propagates_backward_one_step
#check @zero_propagates_int
#check @TwoGlobalTranslationEigen.zero_propagates_one_step₁
#check @TwoGlobalTranslationEigen.zero_propagates_one_step₂
#check @TwoGlobalTranslationEigen.zero_propagates_nat₁
#check @TwoGlobalTranslationEigen.zero_propagates_nat₂
#check @TwoGlobalTranslationEigen.zero_propagates_int₁
#check @TwoGlobalTranslationEigen.zero_propagates_int₂

/-! ## Infinite L3 — Dense-period interface -/

#check @IsPeriod
#check @PeriodSet
#check @DensePeriodSet
#check @period_zero
#check @period_neg
#check @period_add
#check @integer_span_periods
#check @dense_periods_force_const_on_real
#check @TwoIncommensurablePeriodsGenerateDense

/-! ## Infinite L3 — Dense-period coupler -/

#check @IntegerPeriodSpan
#check @two_periods_dense_span_force_const
#check @two_incommensurable_periods_force_const

/-! ## Infinite L3 — Log-derivative coupler scaffolding -/

#check @RealRestrict
#check @ComplexRealPeriod
#check @isPeriod_realRestrict_of_complexRealPeriod
#check @two_complex_real_periods_dense_force_const_on_real
#check @two_incommensurable_complex_real_periods_force_const_on_real

/-! ## Infinite L3 — Exponential survivor concrete scaffolding -/

#check @LogDerivHasComplexRealPeriod
#check @LogDerivCandidate
#check @logDeriv_two_periods_force_const_on_real
#check @logDeriv_two_incommensurable_periods_force_const_on_real
#check @two_shift_logDeriv_constant_on_real

/-! ## Infinite L3 — Translation eigen → log-derivative period interface -/

#check @RealTranslationEigen
#check @LogDerivRespectsRealTranslationEigen
#check @logDeriv_period_of_realTranslationEigen
#check @logDeriv_const_on_real_of_two_realTranslationEigen_denseSpan
#check @logDeriv_const_on_real_of_two_realTranslationEigen

/-! ## Infinite L3 — Log-derivative algebraic cancellation -/

#check @complexLogDeriv
#check @complexLogDeriv_period_of_deriv_eigen
#check @complexLogDeriv_respects_realTranslationEigen_of_deriv_eigen
#check @complexLogDeriv_const_on_real_of_two_realTranslationEigen_denseSpan
#check @complexLogDeriv_const_on_real_of_two_realTranslationEigen

/-! ## Infinite L3 — Translation eigen → derivative eigen (chain-rule step) -/

#check @deriv_eigen_of_realTranslationEigen
#check @complexLogDeriv_period_of_realTranslationEigen
#check @complexLogDeriv_respects_realTranslationEigen
#check @complexLogDeriv_const_on_real_of_two_realTranslationEigen_noDerivHyp_denseSpan
#check @complexLogDeriv_const_on_real_of_two_realTranslationEigen_noDerivHyp
#check @complexLogDeriv_eq_logDeriv

/-! ## Infinite L3 — Log-derivative continuity interface -/

#check @LogDerivContinuousOnReal
#check @continuous_realRestrict_complexLogDeriv
#check @complexLogDeriv_const_on_real_of_two_eigen_denseSpan
#check @complexLogDeriv_const_on_real_of_two_eigen

/-! ## Infinite L3 — Translation defect ↔ real translation eigen coupler -/

#check @realTranslationEigen_of_realLogShiftDefect_eq_zero
#check @realLogShiftDefect_eq_zero_of_realTranslationEigen
#check @complexLogDeriv_const_on_real_of_two_realLogShiftDefects_denseSpan
#check @complexLogDeriv_const_on_real_of_two_realLogShiftDefects

/-! ## Infinite L3 — Sampled who-input → log-derivative constancy -/

#check @realTranslationEigen_of_sampledWhoInput_realShift
#check @complexLogDeriv_const_on_real_of_two_sampledWhoInputs_realShift_denseSpan
#check @complexLogDeriv_const_on_real_of_two_sampledWhoInputs_realShift

/-! ## Infinite L3 — Two-incommensurable sampled who-input wrappers -/

#check @complexLogDeriv_const_on_real_of_twoIncommensurableSampledWhoInputs_realShift_denseSpan
#check @complexLogDeriv_const_on_real_of_twoIncommensurableSampledWhoInputs_realShift

/-! ## Infinite L3 — Log-derivative continuity concrete -/

#check @logDerivContinuousOnReal_of_continuous_deriv
#check @complexLogDeriv_const_on_real_of_two_sampledWhoInputs_realShift_continuousDeriv
#check @complexLogDeriv_const_on_real_of_twoIncomm_sampled_continuousDeriv

/-! ## Infinite L3 — Log-derivative continuity from holomorphicity -/

#check @continuous_deriv_of_complex_differentiable
#check @logDerivContinuousOnReal_of_complex_differentiable
#check @complexLogDeriv_const_on_real_of_two_sampledWhoInputs_realShift_differentiable
#check @complexLogDeriv_const_on_real_of_twoIncomm_sampled_differentiable

/-! ## Infinite L3 — Real-axis constant → globally constant interface -/

#check @ConstantOnRealAxis
#check @GloballyConstant
#check @RealAxisConstExtendsGlobally
#check @constantOnRealAxis_of_pairwise_real_const
#check @globallyConstant_of_realAxisConstExtends
#check @globallyConstant_of_pairwise_real_const
#check @LogDerivRealAxisConstExtendsGlobally
#check @globallyConstant_complexLogDeriv_of_twoIncomm_sampled_differentiable

/-! ## Infinite L3 — Global log-derivative constant → exp survivor interface -/

#check @GlobalLogDerivConstForcesExponentialSurvivor
#check @exponentialSurvivor_of_globalLogDerivConst
#check @exponentialSurvivor_of_twoIncomm_sampled_differentiable
#check @where_rigidity_of_twoIncomm_sampled_differentiable

/-! ## Infinite L3 — Kronecker density (arithmetic half of C1) -/

#check @integerPeriodSpan_eq_addSubgroupClosure_pair
#check @twoIncommensurablePeriodsGenerateDense_of_irrational_div
#check @twoIncommensurablePeriodsGenerateDense_of_incommensurable

/-! ## Infinite L3 — Kronecker pipeline (irrational-ratio inputs) -/

#check @exponentialSurvivor_of_twoIncomm_sampled_differentiable_irrational
#check @where_rigidity_of_twoIncomm_sampled_differentiable_irrational

/-! ## Infinite L3 — Function-level → exponent-level Where lift -/

#check @FunctionWhereForcesExponentReflection
#check @whereKillsExponential_of_functionWhereForcesExponentReflection
#check @where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift

/-! ## Infinite L3 — Real-axis-constant-to-global from analyticity (identity theorem) -/

#check @realAxisConstExtendsGlobally_of_analyticOnNhd
#check @logDerivRealAxisConstExtendsGlobally_of_analyticOnNhd
#check @where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift_analyticLogDeriv

/-! ## Infinite L3 — Reconstruction interface (normalized form) -/

#check @LogDerivEquationSolvesToExp
#check @globalLogDerivConstForcesExponentialSurvivor_of_normalized_solver
#check @where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift_analyticLogDeriv_normalized

/-! ## Infinite L3 — Reconstruction concrete witness (logDeriv_eqOn_iff) -/

#check @logDerivEquationSolvesToExp_of_differentiable_nonvanishing
#check @where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift_analyticLogDeriv_concreteReconstruction

/-! ## Infinite L3 — Function-level Where lift, concrete witness -/

#check @functionWhereForcesExponentReflection_concrete
#check @where_rigidity_concrete_full

/-! ## Infinite L3 — Zero counting (Jensen socket part 1) -/

#check @RealLineZerosInInterval
#check @HasAtMostLinearRealZeros

/-! ## Infinite L3 — Refined zero-density bridge (Jensen socket part 2) -/

#check @FiniteExpTypeLinearZeroBound
#check @LogSampleZeroContradictionReady
#check @LogSampleZeroContradictionWithBound
#check @zeroDensityForcesZero_of_logSampleContradictionReady_unbundled
#check @zeroDensityForcesZero_of_logSampleContradictionWithBound

/-! ## Infinite L3 — Log-sample zero contradiction (counting socket) -/

#check @LinearZeroBoundBeatingLogSample
#check @false_of_linearZeroBoundBeating_sampledZeros
#check @logSampleZeroContradictionReady_of_linearZeroBoundBeating
#check @zeroDensityForcesZero_of_linearZeroBoundBeating

/-! ## Infinite L3 — Odd-log specialization of the linear-beating sample -/

#check @eventually_linear_beats_log
#check @oddLogLinearZeroBoundBeating

/-! ## Infinite L3 — Jensen / Cartwright interface (the last analytic socket) -/

#check @JensenCartwrightLinearZeroBound
#check @zeroDensityForcesZero_oddLog_of_jensenCartwright
#check @oddLogDenseEnough
#check @zeroDensityForcesZero_for_oddLogSample

/-! ## Infinite L3 — Jensen final pipeline (paper-level headline) -/

#check @where_rigidity_of_oddLogSample_from_jensenCartwright

/-! ## Bridge C — functional-equation freezing (real-displacement core) -/

#check @IsRealComplex
#check @IsPureImagComplex
#check @realComplex_of_real
#check @pureImag_mul_I
#check @pureImag_neg
#check @real_mul_pureImag
#check @firstOrderResponse_pureImag_param
#check @firstOrderResponse_pureImag_real
#check @bridgeC_where_firstOrder_freezes_Re
#check @where_firstOrder_response_has_zero_real_part

/-! ## Bridge C, zeta branch — basic scaffold -/

#check @GaussianWhoWhere.ZetaBridge.BridgeA_DirichletLike
#check @GaussianWhoWhere.ZetaBridge.BridgeA_EulerProductLike
#check @GaussianWhoWhere.ZetaBridge.BridgeAprime_LogDerivLike
#check @GaussianWhoWhere.ZetaBridge.CompletedWhereLike
#check @GaussianWhoWhere.ZetaBridge.ZetaBridgeCProfile
#check @GaussianWhoWhere.ZetaBridge.zetaBridgeCProfile_has_where
#check @GaussianWhoWhere.ZetaBridge.zetaBridgeCProfile_has_who_dirichlet
#check @GaussianWhoWhere.ZetaBridge.zetaBridgeCProfile_has_who_euler
#check @GaussianWhoWhere.ZetaBridge.zetaBridgeCProfile_has_logDeriv_bridge

/-! ## Bridge C, zeta branch — concrete Mathlib-backed Dirichlet bridge -/

#check @GaussianWhoWhere.ZetaBridge.rightHalfPlane_gt_one
#check @GaussianWhoWhere.ZetaBridge.zetaDirichletModel
#check @GaussianWhoWhere.ZetaBridge.zetaDirichletModelNatAddOne
#check @GaussianWhoWhere.ZetaBridge.riemannZeta_bridgeA_dirichlet
#check @GaussianWhoWhere.ZetaBridge.riemannZeta_has_dirichlet_bridge
#check @GaussianWhoWhere.ZetaBridge.riemannZeta_bridgeA_dirichlet_natAddOne

/-! ## L-function Bridge C profile -/

#check @GaussianWhoWhere.LFunctionBridge.DirichletSeriesBridge
#check @GaussianWhoWhere.LFunctionBridge.EulerProductBridge
#check @GaussianWhoWhere.LFunctionBridge.LogDerivativeBridge
#check @GaussianWhoWhere.LFunctionBridge.dirichletSeriesBridge_to_BridgeA_DirichletLike
#check @GaussianWhoWhere.LFunctionBridge.eulerProductBridge_to_BridgeA_EulerProductLike
#check @GaussianWhoWhere.LFunctionBridge.logDerivativeBridge_to_BridgeAprime_LogDerivLike
#check @GaussianWhoWhere.LFunctionBridge.LFunctionBridgeCProfile
#check @GaussianWhoWhere.LFunctionBridge.lFunctionBridgeCProfile_has_dirichlet
#check @GaussianWhoWhere.LFunctionBridge.lFunctionBridgeCProfile_has_eulerProduct
#check @GaussianWhoWhere.LFunctionBridge.lFunctionBridgeCProfile_has_logDerivative
#check @GaussianWhoWhere.LFunctionBridge.lFunctionBridgeCProfile_has_where
#check @GaussianWhoWhere.LFunctionBridge.lFunctionBridgeCProfile_to_zetaBridgeCProfile
#check @GaussianWhoWhere.LFunctionBridge.SelbergClassLike
#check @GaussianWhoWhere.LFunctionBridge.lFunctionBridgeCProfile_of_selbergClassLike

/-! ## Concrete zeta `EulerProductBridge` witness -/

#check @GaussianWhoWhere.LFunctionBridge.zetaEulerDomain
#check @GaussianWhoWhere.LFunctionBridge.zetaEulerLocalFactor
#check @GaussianWhoWhere.LFunctionBridge.zetaEulerProductModel
#check @GaussianWhoWhere.LFunctionBridge.riemannZeta_eulerProductBridge
#check @GaussianWhoWhere.LFunctionBridge.riemannZeta_bridgeA_eulerProduct

/-! ## Concrete zeta `LogDerivativeBridge` witness -/

#check @GaussianWhoWhere.LFunctionBridge.zetaLogDerivDomain
#check @GaussianWhoWhere.LFunctionBridge.zetaVonMangoldtModel
#check @GaussianWhoWhere.LFunctionBridge.zetaLogDerivativeModel
#check @GaussianWhoWhere.LFunctionBridge.riemannZeta_logDerivativeBridge
#check @GaussianWhoWhere.LFunctionBridge.riemannZeta_bridgeAprime_logDerivative

end GaussianWhoWhere
