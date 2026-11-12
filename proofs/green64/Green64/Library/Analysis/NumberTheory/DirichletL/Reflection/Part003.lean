module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part014
public import Green64.Library.OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Reflection / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Reflection.PhysicalIntegral -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def finitePhysicalKernelRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ→ℂ) (θ X : ℝ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    actualKernelSourceTerm F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc
      u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X

def weightedFinitePhysicalKernelRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ→ℂ) (θ X : ℝ) (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    (r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val)*actualKernelSourceTerm F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc
      u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X

theorem weighted_finite_physical_row_common_measure
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ)
        (Pset nset bset : Finset (Ideal Eis))
        (D : ∀ P : Pset, IsCoprime K P.val →
          ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode),
        (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) → (∀ n ∈ nset, n≠0) → (∀ b ∈ bset, b≠0) →
        ∀ (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
        weightedFinitePhysicalKernelRow F K hK S jF Pset nset bset D s hc unit m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc
              (fun K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ))
              (fun P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ))
              (fun n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)) unit m) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := actual_reflected_finite_source_uniform
    (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode)
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀
  let T := CoprimeSourceIndex K Pset nset bset
  have hh := he (Finset.univ : Finset T) (fun x => r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val) (fun _ => K) (fun _ => hK)
    (fun x => S x.1.val.val) jF (fun x => D x.1.val x.1.property)
    (fun x => x.2.1.val) (fun x => x.2.2.val)
    (fun x _ => ⟨hn _ x.2.1.property,hb _ x.2.2.property⟩)
  unfold weightedFinitePhysicalKernelRow
  rw [hh]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [T]
  congr 1
  rw [weightedPhysicalReflectedRow_eq_coprime_source]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hprod x.1.val.val x.1.val.property]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.RamifiedWidth -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open CompletedDyadic CompletedGauss
noncomputable section

lemma literal_ramified_log_width (Z : ℝ) (m : ℕ) :
    3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m) =
      (m:ℝ)*Real.logb Z 3 := by
  rw [ramifiedScale,one_mul,Real.logb_pow,completedRamifiedStep,
    Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0:ℝ)<3)]
  ring

lemma literal_ramified_width_offset (Z : ℝ) (m : ℕ) :
    3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m) =
      InverseTerminalWidths.ramifiedWidth Z m + 4*Real.logb Z 3 := by
  rw [literal_ramified_log_width]
  unfold InverseTerminalWidths.ramifiedWidth
  ring

lemma reflectedExponent_ramified_shift (O₀ H S₀ B₀ za v ell el Td δ : ℝ) :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el Td =
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell (el-δ) (Td-δ)-2*δ/3 := by
  unfold InverseTerminalWidths.reflectedExponent
  rw [show Td-δ-v-3*ell-(el-δ)=Td-v-3*ell-el by ring]
  ring

theorem literal_reflectedExponent_le_signed (Z : ℝ) (hZ : 1<Z) (m : ℕ)
    (O₀ H S₀ B₀ za v ell Td : ℝ) :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)) Td ≤
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (InverseTerminalWidths.ramifiedWidth Z m) (Td-4*Real.logb Z 3) := by
  have hδ : 0≤4*Real.logb Z 3 := mul_nonneg (by norm_num) (Real.logb_nonneg hZ (by norm_num))
  rw [reflectedExponent_ramified_shift O₀ H S₀ B₀ za v ell _ Td (4*Real.logb Z 3),
    literal_ramified_width_offset]
  rw [add_sub_cancel_right]
  linarith

theorem ramified_offset_threshold (η : ℝ) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ Z : ℝ, Z₀≤Z →
      0≤4*Real.logb Z 3 ∧ 4*Real.logb Z 3≤η := by
  obtain ⟨Z₀,hZ₀,hw⟩ := InverseTerminalWidths.ramified_width_threshold η hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have he := hw Z hZ 0
  unfold InverseTerminalWidths.ramifiedWidth at he
  norm_num at he
  exact ⟨mul_nonneg (by norm_num) (Real.logb_nonneg hz (by norm_num)),by linarith⟩

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.RawTail -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev RawTailIndex := ℕ×NonzeroDualIdeal×NonzeroDualIdeal

def rawTailWeight (q : ℝ) (x : RawTailIndex) : ℝ :=
  ((q^6)⁻¹)^x.1*((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹

lemma rawTailWeight_nonneg (q : ℝ) (x : RawTailIndex) : 0≤ rawTailWeight q x := by
  unfold rawTailWeight
  positivity

lemma rawTailWeight_summable (q : ℝ) (hq : 1<q) : Summable (rawTailWeight q) := by
  have hq6 : 1<q^6 := one_lt_pow₀ hq (by norm_num)
  have hg : Summable (fun m : ℕ => ((q^6)⁻¹)^m) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).mpr hq6)
  have hi := nonzeroDualIdeal_inv_pow_summable 2 (by norm_num)
  have hj := nonzeroDualIdeal_inv_pow_summable 6 (by norm_num)
  have hh := hg.mul_of_nonneg (hi.mul_of_nonneg hj (fun I => by positivity) (fun J => by positivity))
    (fun m => by positivity) (fun IJ => by positivity)
  exact hh.congr (fun x => by simp only [rawTailWeight]; ring)

lemma tail_power_gain (A : ℕ) (T x : ℝ) (hT : 0<T) (hTx : T≤x) :
    x^(-((A+2:ℕ):ℝ))≤T^(-(A:ℝ))*(x^2)⁻¹ := by
  have hx : 0<x := lt_of_lt_of_le hT hTx
  rw [show -((A+2:ℕ):ℝ)=-(A:ℝ)+(-2) by push_cast; ring,Real.rpow_add hx]
  rw [show x^(-2:ℝ)=(x^2)⁻¹ by rw [Real.rpow_neg hx.le,Real.rpow_two]]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hT hTx (neg_nonpos.mpr (Nat.cast_nonneg A))) (by positivity)

theorem raw_kernel_tail (a b q : ℝ) (ha : 0<a) (hq : 1<q) (A : ℕ) :
    ∃ (S : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc a b →
    ∀ (scale ρ B T : ℝ), 0<scale → 0<ρ → 0≤B → 0<T →
    ∀ (β : ℕ→Ideal Eis→Ideal Eis→ℂ),
      (∀ m, ∀ I J : NonzeroDualIdeal, ‖β m I.val J.val‖≤B) →
    ∀ cut : RawTailIndex→Prop,
      (∀ x, cut x → T≤ scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3) →
    Summable (fun x => ‖if cut x then rawDualKernelTerm V scale ρ q β x else 0‖) ∧
      ‖∑' x, if cut x then rawDualKernelTerm V scale ρ q β x else 0‖≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*B*T^(-(A:ℝ))*(scale^2*ρ^6)⁻¹ := by
  obtain ⟨S,C,hC,hkernel⟩ := CubicReflectionKernel.paperKernel_euler_source_power_decay a b ha (A+2) 0
  let D : ℝ := (∑' x,rawTailWeight q x)+1
  have hsum := rawTailWeight_summable q hq
  have hD : 0<D := by
    have h : 0≤∑' x,rawTailWeight q x := tsum_nonneg (rawTailWeight_nonneg q)
    dsimp only [D]
    linarith
  refine ⟨S,C*D,mul_pos hC hD,?_⟩
  intro V hV scale ρ B T hs hρ hB hT β hβ cut hcut
  let M : ℝ := C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*B*T^(-(A:ℝ))*(scale^2*ρ^6)⁻¹
  have hM : 0≤M := by dsimp only [M]; positivity
  have hmajor : ∀ x : RawTailIndex,
      ‖if cut x then rawDualKernelTerm V scale ρ q β x else 0‖≤M*rawTailWeight q x := by
    intro x
    by_cases hx : cut x
    · rw [ite_eq_left hx,rawDualKernelTerm,norm_mul]
      let arg := scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3
      have harg : 0<arg := lt_of_lt_of_le hT (hcut x hx)
      have hk := (hkernel V hV arg harg).2
      simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hk
      have hp := tail_power_gain A T arg hT (hcut x hx)
      have hk' := hk.trans (mul_le_mul_of_nonneg_left hp (by positivity :
        0≤C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V))
      apply (mul_le_mul (hβ x.1 x.2.1 x.2.2) hk' (norm_nonneg _) hB).trans_eq
      dsimp only [M,arg]
      rw [rawDualKernel_inverse_square]
      unfold rawTailWeight
      ring
    · rw [ite_eq_right hx,norm_zero]
      exact mul_nonneg hM (rawTailWeight_nonneg q x)
  have hn := (hsum.mul_left M).of_nonneg_of_le (fun x => norm_nonneg _) hmajor
  refine ⟨hn,?_⟩
  calc
    _ ≤ ∑' x, ‖if cut x then rawDualKernelTerm V scale ρ q β x else 0‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' x, M*rawTailWeight q x := hn.tsum_le_tsum hmajor (hsum.mul_left M)
    _ = M*(∑' x,rawTailWeight q x) := tsum_mul_left
    _ ≤ M*D := mul_le_mul_of_nonneg_left (by dsimp only [D]; linarith) hM
    _ = _ := by dsimp only [M]; ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.RawCoefficient -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def literalRawCoefficient (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  if Squarefree n ∧ primaryGenerator n≠0 ∧ primaryGenerator b≠0 then
    (s.amplitude u m n b *
      (star D.fixedFactor*ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m n b))*
      ∏ i, mixedActiveBracket G.generator_ne_zero G.generator_good j S D i (s.modelDualNumerator u m n b)) /
        ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ)
  else 0

lemma literalRawCoefficient_norm (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : NonzeroDualIdeal) :
    ‖literalRawCoefficient G D s hc j S u m n.val b.val‖≤(Ideal.absNorm (∏ i,G.ideal i):ℝ) := by
  unfold literalRawCoefficient
  split_ifs
  · have hr : 1≤ ramifiedScale 1 completedRamifiedStep m := by
      simpa only [ramifiedScale,one_mul] using one_le_pow₀ completedRamifiedStep_gt_one.le (n:=m)
    have hn : 1≤Real.sqrt (Ideal.absNorm n.val:ℝ) :=
      (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by simpa using norm_at_least_one n.val n.property)
    have hb := norm_at_least_one b.val b.property
    have hden : 1≤ ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n.val:ℝ)*(Ideal.absNorm b.val:ℝ) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr hn) hb
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (le_trans zero_le_one hden)]
    apply (div_le_div_of_nonneg_right (literal_mixed_coefficient_crude G D s hc hN hbase hchar j hj S u m n.val b.val)
      (le_trans zero_le_one hden)).trans
    exact div_le_self (Nat.cast_nonneg _) hden
  · simp only [norm_zero]
    exact Nat.cast_nonneg _

theorem literal_reflected_raw_tail (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (scale T : ℝ), 0<scale → 0<T →
    ∀ cut : RawTailIndex→Prop,
      (∀ x, cut x → T≤ scale*(ramifiedScale 1 completedRamifiedStep x.1)^3*
        (Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3) →
      Summable (fun x => ‖if cut x then rawDualKernelTerm V scale 1 completedRamifiedStep
        (literalRawCoefficient G D s hc j S u) x else 0‖) ∧
      ‖∑' x, if cut x then rawDualKernelTerm V scale 1 completedRamifiedStep
        (literalRawCoefficient G D s hc j S u) x else 0‖≤
      C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(scale^2)⁻¹ := by
  obtain ⟨orders,C,hC,hb⟩ := raw_kernel_tail a₀ b₀ completedRamifiedStep ha₀ completedRamifiedStep_gt_one A
  refine ⟨orders,C,hC,?_⟩
  intro V hV G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  have hh := hb V hV scale 1 (Ideal.absNorm (∏ i,G.ideal i):ℝ) T hs (by norm_num) (Nat.cast_nonneg _) hT
    (literalRawCoefficient G D s hc j S u) (literalRawCoefficient_norm G D s hc hN hbase hchar j hj S u) cut hcut
  simpa only [one_pow,mul_one] using hh
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.FullRaw -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def thetaRawIndex (t : ThetaFullIndex) : Eisˣ×RawTailIndex :=
  (t.1,t.2.1,⟨t.2.2.1.val,t.2.2.1.property.1.ne_zero⟩,
    ⟨t.2.2.2.val,primaryGenerator_ne_zero_ideal _ t.2.2.2.property⟩)

lemma thetaRawIndex_injective : Function.Injective thetaRawIndex := by
  rintro ⟨u,m,⟨n,hn⟩,⟨b,hb⟩⟩ ⟨v,k,⟨n',hn'⟩,⟨b',hb'⟩⟩ h
  simpa only [thetaRawIndex,Prod.mk.injEq,Subtype.mk.injEq] using h

def literalRawScale (G : PrimeFamily ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (X : ℝ) : ℝ :=
  X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c*∏ i,G.generator i}):ℝ)^2)

lemma literalRawScale_pos (G : PrimeFamily ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (X : ℝ) (hX : 0<X) : 0<literalRawScale G s X := by
  have hn : (0:ℝ)<Ideal.absNorm (Ideal.span {c*∏ i,G.generator i}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun i _ => G.generator_ne_zero i)))))
  have hs := sourceCuspScale_pos s.index
  unfold literalRawScale
  positivity

def literalRawSeries (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) (t : Eisˣ×RawTailIndex) : ℂ :=
  rawDualKernelTerm (Vstar W) (literalRawScale G s X) 1 completedRamifiedStep
    (literalRawCoefficient G D s hc j S t.1) t.2

lemma literalRawSeries_support (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    Function.support (literalRawSeries G D s hc j S W X)⊆Set.range thetaRawIndex := by
  intro t ht
  have hp : Squarefree t.2.2.1.val ∧ primaryGenerator t.2.2.1.val≠0 ∧ primaryGenerator t.2.2.2.val≠0 := by
    by_contra hn
    exact ht (by simp only [literalRawSeries,rawDualKernelTerm,literalRawCoefficient,ite_eq_right hn,zero_mul])
  exact ⟨(t.1,t.2.1,⟨t.2.2.1.val,hp.1,hp.2.1⟩,⟨t.2.2.2.val,hp.2.2⟩),rfl⟩

theorem mixedReflectedValue_eq_fullRaw (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue D s G.generator_ne_zero hc G.generator_good j S W X=
      fixedRadialCoefficientScalar*s.stratumShapeFactor (c*∏ i,G.generator i)*
        ∑' t : Eisˣ×RawTailIndex, literalRawSeries G D s hc j S W X t := by
  unfold mixedReflectedValue
  congr 1
  refine (tsum_congr ?_).trans (thetaRawIndex_injective.tsum_eq (literalRawSeries_support G D s hc j S W X))
  intro t
  have hx : sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)=
      s.modelDualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val := by
    rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
    rfl
  unfold literalRawSeries rawDualKernelTerm literalRawCoefficient thetaRawIndex literalRawScale
  rw [ite_eq_left ⟨t.2.2.1.property.1,t.2.2.1.property.2,t.2.2.2.property⟩,hx]
  dsimp only
  simp only [ramifiedScale, one_mul]
  ring

theorem literalRawSeries_summable_norm (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    Summable (fun t : Eisˣ×RawTailIndex => ‖literalRawSeries G D s hc j S W X t‖) := by
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨?_,(hasSum_fintype _).summable⟩
  intro u
  exact rawDualKernelTerm_summable_norm (Vstar W) lo hi hlo (Vstar_support W lo hi hWs)
    (Vstar_contDiff W lo hi hlo hWs hW) (literalRawScale G s X) 1 completedRamifiedStep
    (Ideal.absNorm (∏ i,G.ideal i):ℝ) (literalRawScale_pos G s hc X hX) (by norm_num)
    completedRamifiedStep_gt_one (Nat.cast_nonneg _) (literalRawCoefficient G D s hc j S u)
    (literalRawCoefficient_norm G D s hc hN hbase hchar j hj S u)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.FullDyadic -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def literalDyadicBlock (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) (u : Eisˣ) (i : ℕ×ℕ×ℕ) : ℂ :=
  ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
    literalRawSeries G D s hc j S W X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)

theorem mixedReflectedValue_eq_dyadic (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    mixedReflectedValue D s G.generator_ne_zero hc G.generator_good j S W X=
      fixedRadialCoefficientScalar*s.stratumShapeFactor (c*∏ i,G.generator i)*
        ∑' u : Eisˣ, ∑' i : ℕ×ℕ×ℕ, literalDyadicBlock G D s hc j S W X u i := by
  have hs := (literalRawSeries_summable_norm G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm
  rw [mixedReflectedValue_eq_fullRaw,hs.tsum_prod]
  congr 1
  apply tsum_congr
  intro u
  exact tsum_dualIdealDyads _ (hs.prod_factor u)

lemma dyadic_kernel_argument_lower (scale rho q : ℝ) (hs : 0≤ scale)
    (hr : 0≤ rho) (hq : 0≤q) (i : ℕ×ℕ×ℕ)
    (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1) :
    scale*(ramifiedScale rho q i.1)^3*(2:ℝ)^i.2.2*((2:ℝ)^i.2.1)^3/16 ≤
      scale*(ramifiedScale rho q i.1)^3*(Ideal.absNorm n.val:ℝ)*(Ideal.absNorm b.val:ℝ)^3 := by
  have hn := (dualIdealDyad_bounds _ _ n.property).2.1
  have hb := (dualIdealDyad_bounds _ _ b.property).2.1
  have hp : 0≤ scale*(ramifiedScale rho q i.1)^3 := by
    unfold ramifiedScale
    positivity
  have hh := mul_le_mul hn (pow_le_pow_left₀ (by positivity) hb 3) (by positivity)
    (Nat.cast_nonneg (Ideal.absNorm n.val))
  have hh' := mul_le_mul_of_nonneg_left hh hp
  nlinarith only [hh']

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.DyadicTail -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def rawDyadicLabel (x : RawTailIndex) : ℕ×ℕ×ℕ :=
  (x.1,Nat.clog 2 (Ideal.absNorm x.2.2.val),Nat.clog 2 (Ideal.absNorm x.2.1.val))

def rawDyadicCenter (scale : ℝ) (i : ℕ×ℕ×ℕ) : ℝ :=
  scale*(ramifiedScale 1 completedRamifiedStep i.1)^3*(2:ℝ)^i.2.2*((2:ℝ)^i.2.1)^3

lemma rawDyadicCenter_lower (scale : ℝ) (hs : 0≤ scale) (x : RawTailIndex) :
    rawDyadicCenter scale (rawDyadicLabel x)/16 ≤
      scale*(ramifiedScale 1 completedRamifiedStep x.1)^3*
        (Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3 := by
  exact dyadic_kernel_argument_lower scale 1 completedRamifiedStep hs (by norm_num)
    (le_trans zero_le_one completedRamifiedStep_gt_one.le) (rawDyadicLabel x)
    ⟨x.2.1.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.1.property,rfl⟩⟩
    ⟨x.2.2.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.2.property,rfl⟩⟩

theorem tsum_cut_dyadic (f : RawTailIndex→ℂ) (cut : (ℕ×ℕ×ℕ)→Prop)
    (hf : Summable (fun x => if cut (rawDyadicLabel x) then f x else 0)) :
    (∑' x, if cut (rawDyadicLabel x) then f x else 0)=
      ∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          f (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
            ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0 := by
  rw [tsum_dualIdealDyads _ hf]
  apply tsum_congr
  intro i
  have hl (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1) :
      rawDyadicLabel (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)=i := by
    simp only [rawDyadicLabel,((mem_dualIdealDyad _ _).mp n.property).2,
      ((mem_dualIdealDyad _ _).mp b.property).2]
  by_cases hi : cut i
  · simp only [hl,ite_eq_left hi]
  · simp only [hl,ite_eq_right hi,Finset.sum_const_zero]

theorem literal_reflected_dyadic_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc lo hi →
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (scale T : ℝ), 0<scale → 0<T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤ rawDyadicCenter scale i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          rawDualKernelTerm V scale 1 completedRamifiedStep
            (literalRawCoefficient G D s hc j S u)
            (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
              ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0‖≤
        C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(scale^2)⁻¹ := by
  obtain ⟨orders,C,hC,hb⟩ := literal_reflected_raw_tail (ι:=ι) (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A
  refine ⟨orders,C,hC,?_⟩
  intro V hV G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  obtain ⟨hn,hh⟩ := hb V hV G D s hc hN hbase hchar j hj S u scale T hs hT
    (fun x => cut (rawDyadicLabel x)) (fun x hx => by
      have hc' := hcut (rawDyadicLabel x) hx
      have hl := rawDyadicCenter_lower scale hs.le x
      linarith)
  rw [tsum_cut_dyadic _ cut hn.of_norm] at hh
  exact hh
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.DyadicBox -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

lemma ramifiedScale_one_cube (m : ℕ) : (ramifiedScale 1 completedRamifiedStep m)^3=(3:ℝ)^m := by
  have hs : completedRamifiedStep^3=(3:ℝ) := by
    unfold completedRamifiedStep
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  simp only [ramifiedScale,one_mul]
  rw [← pow_mul,Nat.mul_comm m 3,pow_mul,hs]

lemma rawDyadicCenter_pow_lower (scale : ℝ) (hs : 0≤ scale) (i : ℕ×ℕ×ℕ) :
    scale*(2:ℝ)^(i.1+i.2.2+3*i.2.1)≤ rawDyadicCenter scale i := by
  unfold rawDyadicCenter
  rw [ramifiedScale_one_cube,pow_add,pow_add,Nat.mul_comm 3 i.2.1,pow_mul]
  simp only [mul_assoc]
  have hm : (2:ℝ)^i.1≤(3:ℝ)^i.1 := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  gcongr

def retainedDyadicBox (scale B : ℝ) : Finset (ℕ×ℕ×ℕ) :=
  let n := columnDyadicLength (max 1 (B/scale))
  (Finset.range (n+1)) ×ˢ ((Finset.range (n+1)) ×ˢ (Finset.range (n+1)))

lemma center_mem_retainedDyadicBox (scale B : ℝ) (hs : 0<scale)
    (i : ℕ×ℕ×ℕ) (hi : rawDyadicCenter scale i≤B) : i∈retainedDyadicBox scale B := by
  let R := max 1 (B/scale)
  have hR : 1≤R := le_max_left _ _
  have hp : (2:ℝ)^(i.1+i.2.2+3*i.2.1)≤R :=
    ((le_div_iff₀ hs).mpr (by nlinarith only [rawDyadicCenter_pow_lower scale hs.le i,hi])).trans (le_max_right _ _)
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^(i.1+i.2.2+3*i.2.1)) hp
  rw [Real.log_pow] at hl
  have hc : ((i.1+i.2.2+3*i.2.1:ℕ):ℝ)≤ columnDyadicLength R := by
    apply le_trans ((le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr hl)
    exact Nat.le_ceil _
  have hc' : i.1+i.2.2+3*i.2.1≤ columnDyadicLength R := by exact_mod_cast hc
  simp only [retainedDyadicBox,Finset.mem_product,Finset.mem_range]
  change i.1<columnDyadicLength R+1 ∧ i.2.1<columnDyadicLength R+1 ∧ i.2.2<columnDyadicLength R+1
  omega

lemma retainedDyadicBox_card (scale B : ℝ) :
    (retainedDyadicBox scale B).card=(columnDyadicLength (max 1 (B/scale))+1)^3 := by
  simp only [retainedDyadicBox,Finset.card_product,Finset.card_range]
  ring

theorem retainedDyadicBox_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ scale B : ℝ,
      ((retainedDyadicBox scale B).card:ℝ)^2≤C*(max 1 (B/scale))^ε := by
  refine ⟨(2+1/((ε/6)*Real.log 2))^6,by positivity,?_⟩
  intro scale B
  have hR : 1≤ max 1 (B/scale) := le_max_left _ _
  have hp : 0< max 1 (B/scale) := lt_of_lt_of_le zero_lt_one hR
  have hh := columnDyadicLength_small_power (ε/6) (by positivity) _ hR
  rw [retainedDyadicBox_card]
  push_cast
  rw [← pow_mul]
  norm_num only [show (3:ℕ)*2=6 by norm_num]
  apply (pow_le_pow_left₀ (by positivity) hh 6).trans_eq
  rw [mul_pow,← Real.rpow_mul_natCast hp.le]
  congr 2
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.HeightTail -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

theorem literal_dyadic_tail_uniform_height (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (θ X T : ℝ), 0<X → 0<T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤ rawDyadicCenter (literalRawScale G s X) i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by
  obtain ⟨orders,C,hC,hbound⟩ := literal_reflected_dyadic_tail (ι:=ι) (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A
  let V := vstarSchwartz W lo hi hlo hWs hW
  have hV : Function.support (V : ℝ→ℂ)⊆Set.Icc lo hi := Vstar_support W lo hi hWs
  obtain ⟨H,hH,hpoly⟩ := CompletedHeight.normTwistedSource_schwartz V lo hi hlo hV
  obtain ⟨degree,C₁,hC₁,hsemi⟩ := hpoly orders
  have hlink (θ : ℝ) : (H θ : ℝ→ℂ)=Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hH θ x]
    change FourierBridge.logPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x)=
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase θ (Real.log x)*W x)
    ring
  have hHs (θ : ℝ) : Function.support (H θ : ℝ→ℂ)⊆Set.Icc lo hi := by
    intro x hx
    change H θ x≠0 at hx
    rw [hH θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  refine ⟨degree,C*C₁,mul_pos hC hC₁,?_⟩
  intro G D s hc hN hbase hchar j hj S u θ X T hX hT cut hcut
  have hh := hbound (H θ) (hHs θ) G D s hc hN hbase hchar j hj S u
    (literalRawScale G s X) T (literalRawScale_pos G s hc X hX) hT cut hcut
  have hleft : (∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          rawDualKernelTerm (H θ) (literalRawScale G s X) 1 completedRamifiedStep
            (literalRawCoefficient G D s hc j S u)
            (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
              ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0)=
      ∑' i : ℕ×ℕ×ℕ, if cut i then
        literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0 := by
    simp only [rawDualKernelTerm,hlink,literalDyadicBlock,literalRawSeries]
  rw [hleft] at hh
  apply hh.trans
  have hsemi' := mul_le_mul_of_nonneg_left (hsemi θ) hC.le
  have hrest : 0≤(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by positivity
  calc
    _ = (C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) (H θ))*
        ((Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹) := by ring
    _ ≤ (C*(C₁*(1+‖θ‖)^degree))*
        ((Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹) :=
      mul_le_mul_of_nonneg_right hsemi' hrest
    _ = _ := by ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.ShellSource -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma shell_windows_one (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (K P : Ideal Eis) (hK : K≠0) (hP : P≠0)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP)
    (j k : ℕ) (n : dualIdealDyad k) (b : dualIdealDyad j) :
    (∏ i : Fin 4, completedShellWindow (kernelLogCoordinates QK QP ((2:ℝ)^k) ((2:ℝ)^j)
      (Ideal.absNorm K:ℝ) (Ideal.absNorm P:ℝ) (Ideal.absNorm n.val:ℝ) (Ideal.absNorm b.val:ℝ) i))=1 := by
  have hnorm (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hn := dualIdealDyad_bounds k n.val n.property
  have hb := dualIdealDyad_bounds j b.val b.property
  apply Finset.prod_eq_one
  intro i hi
  fin_cases i <;> dsimp only [kernelLogCoordinates, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact completedShellWindow_log _ _ (hnorm K hK) hQK hKr.1 hKr.2
  · exact completedShellWindow_log _ _ (hnorm P hP) hQP hPr.1 hPr.2
  · exact completedShellWindow_log _ _ (hnorm n.val hn.1) (by positivity) hn.2.1 hn.2.2
  · exact completedShellWindow_log _ _ (hnorm b.val hb.1) (by positivity) hb.2.1 hb.2.2

theorem literalRawSeries_eq_shell_source (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1)
    (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    literalRawSeries (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)=
    if CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0 then
      actualKernelSourceTerm F K hK S jF D s hc u i.1 n.val b.val
        (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X else 0 := by
  have hw := shell_windows_one QK QP hQK hQP K (∏ i,S.ideal i) hK.1
    (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))) hKr hPr i.2.1 i.2.2 n b
  by_cases hp : CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0
  · have hp' : Squarefree n.val ∧ primaryGenerator n.val≠0 ∧ primaryGenerator b.val≠0 :=
      ⟨hp.1.1,hp.1.2,hp.2⟩
    rw [ite_eq_left hp]
    unfold literalRawSeries rawDualKernelTerm literalRawCoefficient actualKernelSourceTerm actualMixedCoefficient literalRawScale
    rw [ite_eq_left hp',hw]
    dsimp only
    simp only [ramifiedScale,one_mul]
    ring
  · have hp' : ¬(Squarefree n.val ∧ primaryGenerator n.val≠0 ∧ primaryGenerator b.val≠0) :=
      fun h => hp ⟨⟨h.1,h.2.1⟩,h.2.2⟩
    simp only [ite_eq_right hp,literalRawSeries,rawDualKernelTerm,literalRawCoefficient,ite_eq_right hp',zero_mul]

theorem literalDyadicBlock_eq_shell_source (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i=
      ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
        if CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0 then
          actualKernelSourceTerm F K hK S jF D s hc u i.1 n.val b.val
            (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X else 0 := by
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  exact literalRawSeries_eq_shell_source F K hK S jF D s hc u i n b QK QP hQK hQP hKr hPr W θ X
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.ShellDomains -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def reflectedNDyad (k : ℕ) : Finset (Ideal Eis) :=
  (dualIdealDyad k).filter CubicSieve.Admissible

def reflectedBDyad (j : ℕ) : Finset (Ideal Eis) :=
  (dualIdealDyad j).filter (fun b => primaryGenerator b≠0)

lemma reflectedNDyad_bounds (k : ℕ) : ∀ n∈reflectedNDyad k,
    CubicSieve.Admissible n ∧ (2:ℝ)^k/2≤(Ideal.absNorm n:ℝ) ∧ (Ideal.absNorm n:ℝ)≤(2:ℝ)^k := by
  intro n hn
  exact ⟨(Finset.mem_filter.mp hn).2,(dualIdealDyad_bounds k n (Finset.mem_filter.mp hn).1).2⟩

lemma reflectedBDyad_bounds (j : ℕ) : ∀ b∈reflectedBDyad j,
    primaryGenerator b≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm b:ℝ) ∧ (Ideal.absNorm b:ℝ)≤(2:ℝ)^j := by
  intro b hb
  exact ⟨(Finset.mem_filter.mp hb).2,(dualIdealDyad_bounds j b (Finset.mem_filter.mp hb).1).2⟩

lemma double_sum_coe (A B : Finset (Ideal Eis)) (f : Ideal Eis→Ideal Eis→ℂ) :
    (∑ n : A, ∑ b : B, f n.val b.val)=∑ n∈A, ∑ b∈B, f n b := by
  rw [Finset.sum_coe_sort A (fun n : Ideal Eis => ∑ b : B, f n b.val)]
  apply Finset.sum_congr rfl
  intro n hn
  exact Finset.sum_coe_sort B (f n)

lemma sum_dual_mask (j k : ℕ) (f : Ideal Eis→Ideal Eis→ℂ) :
    (∑ n : dualIdealDyad k, ∑ b : dualIdealDyad j,
      if CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0 then f n.val b.val else 0)=
      ∑ n : reflectedNDyad k, ∑ b : reflectedBDyad j, f n.val b.val := by
  rw [double_sum_coe (dualIdealDyad k) (dualIdealDyad j)
    (fun n b => if CubicSieve.Admissible n ∧ primaryGenerator b≠0 then f n b else 0),
    double_sum_coe (reflectedNDyad k) (reflectedBDyad j) f]
  simp only [reflectedNDyad,reflectedBDyad,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn' : CubicSieve.Admissible n
  · simp only [hn',true_and,ite_eq_left]
  · simp only [hn',false_and,ite_false,Finset.sum_const_zero]

theorem literalDyadicBlock_eq_filtered_source (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i=
      ∑ n : reflectedNDyad i.2.2, ∑ b : reflectedBDyad i.2.1,
        actualKernelSourceTerm F K hK S jF D s hc u i.1 n.val b.val
          (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X := by
  rw [literalDyadicBlock_eq_shell_source F K hK S jF D s hc u i QK QP hQK hQP hKr hPr W θ X]
  exact sum_dual_mask i.2.1 i.2.2 (fun n b => actualKernelSourceTerm F K hK S jF D s hc u i.1 n b
    (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.ShellRows -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def literalDyadicRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    literalDyadicBlock (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc
      (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) X u i

theorem literalDyadicRow_eq_physical (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hprod : ∀ P∈Pset, (∏ j,(S P).ideal j)=P)
    (hPr : ∀ P∈Pset, QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) :
    literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw=
      weightedFinitePhysicalKernelRow F K hK S jF Pset (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
        D s hc u i.1 (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
        W θ X r aw (fun _ _ => 1) := by
  unfold literalDyadicRow weightedFinitePhysicalKernelRow CoprimeSourceIndex
  simp only [Fintype.sum_prod_type,mul_one]
  apply Finset.sum_congr rfl
  intro P hP
  have hp : QP/2≤(Ideal.absNorm (∏ j,(S P.val.val).ideal j):ℝ) ∧
      (Ideal.absNorm (∏ j,(S P.val.val).ideal j):ℝ)≤QP := by
    rw [hprod P.val.val P.val.property]
    exact hPr P.val.val P.val.property
  rw [literalDyadicBlock_eq_filtered_source F K hK (S P.val.val) jF (D P.val P.property)
    s hc u i QK QP hQK hQP hKr hp W θ X]
  simp only [Finset.mul_sum]
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.SumEnergy -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem summed_actual_weighted_reflected_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ K ∈ rows, ‖r K‖ ≤ 1) → (∀ P ∈ Pset, ‖aw P‖ ≤ 1) → (∀ n b, ‖w n b‖ ≤ 1) →
      (∑ K ∈ rows, ‖∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2) ≤
      (Fintype.card (φ→Fin 3):ℝ) * ∑ e : φ→Fin 3,
        let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
        let Bq := extractedDualScale (frozenExtracted F jF e 2) B
        (frozenBranchScale F jF e)^2*
          (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := actual_weighted_reflected_branch_energy (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP hr haw hw
  calc
    _ ≤ ∑ K ∈ rows, (Fintype.card (φ→Fin 3):ℝ)*
        ∑ e : φ→Fin 3, ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2 := by
      apply Finset.sum_le_sum
      intro K hK
      simpa only [Finset.card_univ] using CubicEisenstein.norm_sum_sq_le_card Finset.univ
        (fun e : φ→Fin 3 => weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K)
    _ = (Fintype.card (φ→Fin 3):ℝ)*∑ e : φ→Fin 3, ∑ K ∈ rows,
        ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he'
      exact he X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
        G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP hr haw hw

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.SumMeasure -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

theorem integrated_summed_actual_reflected_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (μ : Measure Ω) (density : Ω → ℂ) (scalar : ℂ)
      (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      Integrable density μ →
      (∀ K ∈ rows, AEStronglyMeasurable (fun t => r t K) μ) →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ) →
      (∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) →
      (∀ t, ∀ K ∈ rows, ‖r t K‖ ≤ 1) → (∀ t, ∀ P ∈ Pset, ‖aw t P‖ ≤ 1) →
      (∀ t n b, ‖w t n b‖ ≤ 1) →
      (∑ K ∈ rows, ‖scalar * ∫ t, density t * (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2) ≤
      ‖scalar‖^2*((Fintype.card (φ→Fin 3):ℝ)*∑ e : φ→Fin 3,
          let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
          let Bq := extractedDualScale (frozenExtracted F jF e 2) B
          (frozenBranchScale F jF e)^2*
            (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(∫ t, ‖density t‖ ∂μ)^2 := by
  obtain ⟨C,hC,he⟩ := summed_actual_weighted_reflected_energy (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
  let E : ℝ := (Fintype.card (φ→Fin 3):ℝ)*∑ e : φ→Fin 3,
          let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
          let Bq := extractedDualScale (frozenExtracted F jF e 2) B
          (frozenBranchScale F jF e)^2*
            (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ)))
  have hE : 0 ≤ E := by
    dsimp only [E]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro e he
    have hYq : 0 ≤ extractedDualScale (frozenExtracted F jF e 1) Y := le_trans zero_le_one (le_max_left _ _)
    have hBq : 0 ≤ extractedDualScale (frozenExtracted F jF e 2) B := le_trans zero_le_one (le_max_left _ _)
    positivity
  let ψ : rows → Ω → ℂ := fun K t => (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val)
  have hbound (t : Ω) : (∑ K, ‖ψ K t‖^2) ≤ E := by
    change (∑ K : rows, ‖(∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val)‖^2) ≤ E
    rw [Finset.sum_coe_sort rows (fun K : Ideal Eis => ‖(∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K)‖^2)]
    exact he X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
      G0 D0 u m rows nset bset Pset S (r t) (aw t) (w t)
      hrows hrowcop hproducts hScop hSN hSchar hn hb hP (hr t) (haw t) (hw t)
  have hψM (K : rows) : AEStronglyMeasurable (ψ K) μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro e he
    exact weightedReflectedBranchHybridRow_aestronglyMeasurable μ F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K.val
      (hrM K.val K.property) hawM hwM
  have hpoint (K : rows) (t : Ω) : ‖ψ K t‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖ψ j t‖) (Finset.mem_univ K)).trans (hbound t)
  have hint (K : rows) : Integrable (fun t => density t*ψ K t) μ :=
    hdensity.mul_bdd (hψM K) (Filter.Eventually.of_forall (hpoint K))
  have hh := mul_le_mul_of_nonneg_left
    (common_measure_energy μ density ψ E hE hdensity.norm hint hbound) (sq_nonneg ‖scalar‖)
  have hsum : (∑ K : rows, ‖∫ t, density t*ψ K t ∂μ‖^2) =
      ∑ K ∈ rows, ‖∫ t, density t*(∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2 :=
    Finset.sum_coe_sort rows (fun K : Ideal Eis =>
      ‖∫ t, density t*(∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2)
  rw [hsum] at hh
  simp only [norm_mul,mul_pow,← Finset.mul_sum]
  simpa only [E,mul_assoc] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.PhysicalBranchMeasure -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem weighted_finite_physical_row_branch_measure
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ)
        (Pset nset bset : Finset (Ideal Eis))
        (D : ∀ P : Pset, IsCoprime K P.val →
          ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode),
        (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) → (∀ n ∈ nset, n≠0) → (∀ b ∈ bset, b≠0) →
        ∀ (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
        ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
          (D0 : ControlledStratumArithmetic G0.generator N a c mode),
        (∀ P : Pset, IsCoprime K P.val → Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal)) →
        (∀ P hp, (D P hp).fixedFactor=D0.fixedFactor) →
        (∀ P hp u m n b, actualCuspColumn (D P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
        (∀ b ∈ bset, primaryGenerator b≠0) →
        weightedFinitePhysicalKernelRow F K hK S jF Pset nset bset D s hc unit m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
              (actualCuspColumn D0 s hc unit m)
              (fun K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ))
              (fun P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ))
              (fun n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)) unit m Pset nset bset K)) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := weighted_finite_physical_row_common_measure
    (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode)
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀ ι _ G0 D0 hcop hκ hA hbgen
  rw [he K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  exact weightedPhysicalReflectedRow_eq_branches F K hK S jF Pset nset bset hprod D hcop
    G0 D0 s hc hκ hA hbgen _ _ _ unit m

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.KernelAdmissible -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory FourierBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma weightedKernelCoordinate_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1) (hs : ∀ i y, windows i y≠0 → |y|≤M i)
    (a : ℂ) (ha : ‖a‖≤1) (i : Fin 4) (slope Q t q : ℝ) :
    ‖a*kernelCoordinateWeight (reciprocalKernelWindows windows M i) slope Q t q‖≤1 := by
  rw [norm_mul,kernelCoordinateWeight_norm]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (reciprocalKernelWindows_norm windows M hw hs i _)

lemma weightedKernelDual_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1) (hs : ∀ i y, windows i y≠0 → |y|≤M i)
    (a : ℂ) (ha : ‖a‖≤1) (Qn Qb t n b : ℝ) :
    ‖a*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t n b‖≤1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans
    (kernelDualWeight_norm_le_one _ (reciprocalKernelWindows_norm windows M hw hs) Qn Qb t n b)

lemma weightedKernelCoordinate_measurable (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (a : ℂ) (i : Fin 4) (slope Q q : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      a*kernelCoordinateWeight (reciprocalKernelWindows windows M i) slope Q t q) :=
  ((kernelCoordinateWeight_continuous _ _ _ _).const_mul a).aestronglyMeasurable

lemma weightedKernelDual_measurable (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (a : ℂ) (Qn Qb n b : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      a*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t n b) := by
  exact (((kernelCoordinateWeight_continuous _ _ _ _).mul
    (kernelCoordinateWeight_continuous _ _ _ _)).const_mul a).aestronglyMeasurable

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.PhysicalEnergy -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem finite_physical_source_energy
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C₀ C : ℝ), 0≤C₀ ∧ 0<C ∧
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ)≤X)
      (D : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
        ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property).1 (S P.val)).generator N a c mode)
      (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis⧸(F.sum (S P)).ideal i)≠2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y) →
      (∀ b ∈ bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L) →
      (∀ K P hp, (D K P hp).fixedFactor=D0.fixedFactor) →
      (∀ K P hp u m n b, actualCuspColumn (D K P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
      (∀ K ∈ rows, ‖r₀ K‖≤1) → (∀ P ∈ Pset, ‖aw₀ P‖≤1) → (∀ n b, ‖w₀ n b‖≤1) →
      let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
      let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R
      (∑ K : rows, ‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      scalar^2*((Fintype.card (φ→Fin 3):ℝ)*∑ e : φ→Fin 3,
        let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
        let Bq := extractedDualScale (frozenExtracted F jF e 2) B
        (frozenBranchScale F jF e)^2*
          (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨C,hC,henergy⟩ := integrated_summed_actual_reflected_energy
    (Ω := ℝ) (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode) ε hε
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsource⟩ := weighted_finite_physical_row_branch_measure
    (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode)
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW 0
  refine ⟨degree,C₀,C,hC₀,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
  let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R
  let density := twistedDensity U W θ R
  let r := fun t K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ)
  let aw := fun t P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ)
  let w := fun t n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)
  obtain ⟨hsource',hdi,_,hl1,_⟩ := hsource F s hc u m θ T QK QP Qn Qb hT hQK hQP hQn hQb
  have hpair (K : rows) (P : Pset) (hKP : IsCoprime K.val P.val) :
      Pairwise (Function.onFun IsCoprime (F.reflected K.val (hrows K.val K.property).1 (S P.val)).ideal) := by
    apply F.reflected_pairwise _ _ _ hF
    · intro i j hij
      change IsCoprime ((F.sum (S P.val)).ideal (Sum.inr i)) ((F.sum (S P.val)).ideal (Sum.inr j))
      exact hScop P.val P.property (Sum.inr_injective.ne hij)
    · rw [hproducts P.val P.property]
      exact hKP
    · exact (hrowcop K.val K.property).1
    · intro f i
      change IsCoprime ((F.sum (S P.val)).ideal (Sum.inl f)) ((F.sum (S P.val)).ideal (Sum.inr i))
      exact hScop P.val P.property (Sum.inl_ne_inr : (Sum.inl f : φ⊕σ)≠Sum.inr i)
  have hn0 : ∀ n ∈ nset, n≠0 := fun n hn' => (hn n hn').1.1.ne_zero
  have hb0 : ∀ b ∈ bset, b≠0 := by
    intro b hb' hbzero
    exact (hb b hb').1 (by rw [hbzero,primaryGenerator_zero])
  have hidentity (K : rows) :
      weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀ =
      (scalar:ℂ)*∫ t : ℝ, density t*∑ e : φ→Fin 3,
        weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor (actualCuspColumn D0 s hc u m)
          (r t) (aw t) (w t) u m Pset nset bset K.val :=
    hsource' K.val (hrows K.val K.property).1 S jF Pset nset bset (D K) hproducts hn0 hb0 r₀ aw₀ w₀
      G0 D0 (hpair K) (hκ K) (hA K) (fun b hb' => (hb b hb').1)
  have hh := henergy X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m rows nset bset Pset S volume density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdi
    (fun K hK => weightedKernelCoordinate_measurable windows M (r₀ K) 0 (-2) QK _)
    (fun P hP => weightedKernelCoordinate_measurable windows M (aw₀ P) 1 (-2) QP _)
    (fun n hn b hb => weightedKernelDual_measurable windows M (w₀ n b) Qn Qb _ _)
    (fun t K hK => weightedKernelCoordinate_norm windows M hwindowNorm hwindows _ (hr₀ K hK) _ _ _ _ _)
    (fun t P hP => weightedKernelCoordinate_norm windows M hwindowNorm hwindows _ (haw₀ P hP) _ _ _ _ _)
    (fun t n b => weightedKernelDual_norm windows M hwindowNorm hwindows _ (hw₀ n b) _ _ _ _ _)
  have hR : 0<R := by
    have hCC := actualKernelCoefficient_pos F s hc m T hT
    dsimp only [R,kernelCenter]
    positivity
  have hscalar : 0<scalar := by
    have hr := ramifiedScale_pos 1 completedRamifiedStep (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) m
    have hs := smallScalar_pos hR
    dsimp only [scalar]
    positivity
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hscalar] at hh
  have hl1' : (∫ t : ℝ, ‖density t‖)≤C₀*(1+‖θ‖)^degree := by
    simpa only [pow_zero,one_mul] using hl1
  have hsquare : (∫ t : ℝ, ‖density t‖)^2≤(C₀*(1+‖θ‖)^degree)^2 :=
    (sq_le_sq₀ (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)).mpr hl1'
  simp_rw [hidentity]
  rw [Finset.sum_coe_sort rows (fun K : Ideal Eis => ‖(scalar:ℂ)*∫ t : ℝ, density t*∑ e : φ→Fin 3,
    weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor (actualCuspColumn D0 s hc u m)
      (r t) (aw t) (w t) u m Pset nset bset K‖^2)]
  apply hh.trans
  apply mul_le_mul_of_nonneg_left hsquare
  apply mul_nonneg (sq_nonneg _)
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro e he
  have hYq : 0≤extractedDualScale (frozenExtracted F jF e 1) Y := le_trans zero_le_one (le_max_left _ _)
  have hBq : 0≤extractedDualScale (frozenExtracted F jF e 2) B := le_trans zero_le_one (le_max_left _ _)
  positivity

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Surviving -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {a c : Eis} {mode : Bool}

def survivingFrozenBranches (F : PrimeFamily φ) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) : Finset (φ→Fin 3) :=
  Finset.univ.filter (fun e => ∃ n∈nset, ∃ b∈bset, frozenBranchColumn F jF e A n b≠0)

lemma mem_survivingFrozenBranches (F : PrimeFamily φ) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) (e : φ→Fin 3) :
    e∈survivingFrozenBranches F jF A nset bset ↔
      ∃ n∈nset, ∃ b∈bset, frozenBranchColumn F jF e A n b≠0 := by
  simp [survivingFrozenBranches]

lemma frozenBranchColumn_weight (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (A w : Ideal Eis→Ideal Eis→ℂ) (n b : Ideal Eis) :
    frozenBranchColumn F jF e (fun n b => A n b*w n b) n b =
      w n b*frozenBranchColumn F jF e A n b := by
  unfold frozenBranchColumn
  ring

lemma weighted_branch_zero_of_not_surviving (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (S : Ideal Eis→PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis→Ideal Eis→ℂ)
    (r aw : Ideal Eis→ℂ) (w : Ideal Eis→Ideal Eis→ℂ) (u : Eisˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis)
    (he : e∉survivingFrozenBranches F jF A nset bset) :
    weightedReflectedBranchHybridRow F jF e S s κ A r aw w u m Pset nset bset K=0 := by
  have hz : ∀ n∈nset, ∀ b∈bset, frozenBranchColumn F jF e A n b=0 := by
    intro n hn b hb
    by_contra h
    exact he ((mem_survivingFrozenBranches F jF A nset bset e).mpr ⟨n,hn,b,hb,h⟩)
  unfold weightedReflectedBranchHybridRow hybridRow hybridInner
  simp only [frozenBranchColumn_weight]
  have hi (P : Ideal Eis) : (∑ n∈nset, ∑ b∈bset,
      w n b*frozenBranchColumn F jF e A n b * quadraticRow K (primaryGenerator (n*b))*
        inverseCubicKernel P n*(if IsCoprime P b then 1 else 0))=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    apply Finset.sum_eq_zero
    intro b hb
    simp [hz n hn b hb]
  simp only [hi,mul_zero,Finset.sum_const_zero]

lemma sum_branches_eq_surviving (F : PrimeFamily φ) (jF : φ→ℕ)
    (S : Ideal Eis→PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis→Ideal Eis→ℂ)
    (r aw : Ideal Eis→ℂ) (w : Ideal Eis→Ideal Eis→ℂ) (u : Eisˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis) :
    (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s κ A r aw w u m Pset nset bset K)=
    ∑ e∈survivingFrozenBranches F jF A nset bset,
      weightedReflectedBranchHybridRow F jF e S s κ A r aw w u m Pset nset bset K := by
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro e _ he
  exact weighted_branch_zero_of_not_surviving F jF e S s κ A r aw w u m Pset nset bset K he

theorem surviving_forced_norms (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) (Y B : ℝ)
    (hn : ∀ n∈nset, primaryGenerator n≠0 ∧ (Ideal.absNorm n:ℝ)≤Y)
    (hb : ∀ b∈bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B)
    (e : φ→Fin 3) (he : e∈survivingFrozenBranches F jF A nset bset) :
    (Ideal.absNorm (frozenExtracted F jF e 1):ℝ)≤Y ∧
    (Ideal.absNorm (frozenExtracted F jF e 2):ℝ)≤B := by
  obtain ⟨n,hn',b,hb',hz⟩ := (mem_survivingFrozenBranches F jF A nset bset e).mp he
  obtain ⟨hd1,hd2,_⟩ := frozenBranchColumn_divisibility F hF jF e A n b (hn n hn').1 (hb b hb').1 hz
  have hn0 : n≠0 := by intro h; exact (hn n hn').1 (by rw [h,primaryGenerator_zero])
  have hb0 : b≠0 := by intro h; exact (hb b hb').1 (by rw [h,primaryGenerator_zero])
  have hnpos : 0<Ideal.absNorm n := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn0)
  have hbpos : 0<Ideal.absNorm b := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hb0)
  constructor
  · exact le_trans (by exact_mod_cast Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm hd1)) (hn n hn').2
  · exact le_trans (by exact_mod_cast Nat.le_of_dvd hbpos (map_dvd Ideal.absNorm hd2)) (hb b hb').2

theorem surviving_extracted_scales (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) (Y B : ℝ)
    (hn : ∀ n∈nset, primaryGenerator n≠0 ∧ (Ideal.absNorm n:ℝ)≤Y)
    (hb : ∀ b∈bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B)
    (e : φ→Fin 3) (he : e∈survivingFrozenBranches F jF A nset bset) :
    extractedDualScale (frozenExtracted F jF e 1) Y = Y/Ideal.absNorm (frozenExtracted F jF e 1) ∧
    extractedDualScale (frozenExtracted F jF e 2) B = B/Ideal.absNorm (frozenExtracted F jF e 2) := by
  have h := surviving_forced_norms F hF jF A nset bset Y B hn hb e he
  have hp (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  exact ⟨max_eq_right ((one_le_div (hp 1)).mpr h.1),
    max_eq_right ((one_le_div (hp 2)).mpr h.2)⟩

theorem surviving_frozen_local_assignments (F : PrimeFamily φ) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis))
    (e : φ→Fin 3) (he : e∈survivingFrozenBranches F jF A nset bset) :
    ∃ n∈nset, ∃ b∈bset, ∀ i,
      (jF i≠4 → e i=0) ∧
      (jF i=4 → e i=1 → primaryGenerator n∈F.ideal i) ∧
      (jF i=4 → e i=2 → primaryGenerator n∉F.ideal i ∧ primaryGenerator b∈F.ideal i) := by
  obtain ⟨n,hn,b,hb,hz⟩ := (mem_survivingFrozenBranches F jF A nset bset e).mp he
  refine ⟨n,hn,b,hb,?_⟩
  have hh := (mul_ne_zero_iff.mp hz).2
  intro i
  have hi := (Finset.prod_ne_zero_iff.mp hh) i (Finset.mem_univ i)
  simpa only [PrimeFamily.generator_span] using
    InverseTerminalWidths.surviving_local_piece (Ideal.span {F.generator i}) (F.generator_good i)
      (jF i) (e i) (primaryGenerator n) (primaryGenerator b) hi

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.FilteredEnergy -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem filtered_actual_weighted_reflected_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ) (E : Finset (φ→Fin 3))
      (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ K ∈ rows, ‖r K‖ ≤ 1) → (∀ P ∈ Pset, ‖aw P‖ ≤ 1) → (∀ n b, ‖w n b‖ ≤ 1) →
      (∑ K ∈ rows, ‖∑ e∈E, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2) ≤
      (E.card:ℝ) * ∑ e∈E,
        let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
        let Bq := extractedDualScale (frozenExtracted F jF e 2) B
        (frozenBranchScale F jF e)^2*
          (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := actual_weighted_reflected_branch_energy (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S E r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP hr haw hw
  calc
    _ ≤ ∑ K ∈ rows, (E.card:ℝ)*
        ∑ e∈E, ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2 := by
      apply Finset.sum_le_sum
      intro K hK
      exact CubicEisenstein.norm_sum_sq_le_card E
        (fun e : φ→Fin 3 => weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K)
    _ = (E.card:ℝ)*∑ e∈E, ∑ K ∈ rows,
        ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he'
      exact he X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
        G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP hr haw hw

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.FilteredMeasure -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

theorem integrated_filtered_actual_reflected_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ) (branches : Finset (φ→Fin 3))
      (μ : Measure Ω) (density : Ω → ℂ) (scalar : ℂ)
      (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      Integrable density μ →
      (∀ K ∈ rows, AEStronglyMeasurable (fun t => r t K) μ) →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ) →
      (∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) →
      (∀ t, ∀ K ∈ rows, ‖r t K‖ ≤ 1) → (∀ t, ∀ P ∈ Pset, ‖aw t P‖ ≤ 1) →
      (∀ t n b, ‖w t n b‖ ≤ 1) →
      (∑ K ∈ rows, ‖scalar * ∫ t, density t * (∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2) ≤
      ‖scalar‖^2*((branches.card:ℝ)*∑ e∈branches,
          let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
          let Bq := extractedDualScale (frozenExtracted F jF e 2) B
          (frozenBranchScale F jF e)^2*
            (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(∫ t, ‖density t‖ ∂μ)^2 := by
  obtain ⟨C,hC,he⟩ := filtered_actual_weighted_reflected_energy (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S branches μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
  let E : ℝ := (branches.card:ℝ)*∑ e∈branches,
          let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
          let Bq := extractedDualScale (frozenExtracted F jF e 2) B
          (frozenBranchScale F jF e)^2*
            (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ)))
  have hE : 0 ≤ E := by
    dsimp only [E]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro e he
    have hYq : 0 ≤ extractedDualScale (frozenExtracted F jF e 1) Y := le_trans zero_le_one (le_max_left _ _)
    have hBq : 0 ≤ extractedDualScale (frozenExtracted F jF e 2) B := le_trans zero_le_one (le_max_left _ _)
    positivity
  let ψ : rows → Ω → ℂ := fun K t => (∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val)
  have hbound (t : Ω) : (∑ K, ‖ψ K t‖^2) ≤ E := by
    change (∑ K : rows, ‖(∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val)‖^2) ≤ E
    rw [Finset.sum_coe_sort rows (fun K : Ideal Eis => ‖(∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K)‖^2)]
    exact he X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
      G0 D0 u m rows nset bset Pset S branches (r t) (aw t) (w t)
      hrows hrowcop hproducts hScop hSN hSchar hn hb hP (hr t) (haw t) (hw t)
  have hψM (K : rows) : AEStronglyMeasurable (ψ K) μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro e he
    exact weightedReflectedBranchHybridRow_aestronglyMeasurable μ F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K.val
      (hrM K.val K.property) hawM hwM
  have hpoint (K : rows) (t : Ω) : ‖ψ K t‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖ψ j t‖) (Finset.mem_univ K)).trans (hbound t)
  have hint (K : rows) : Integrable (fun t => density t*ψ K t) μ :=
    hdensity.mul_bdd (hψM K) (Filter.Eventually.of_forall (hpoint K))
  have hh := mul_le_mul_of_nonneg_left
    (common_measure_energy μ density ψ E hE hdensity.norm hint hbound) (sq_nonneg ‖scalar‖)
  have hsum : (∑ K : rows, ‖∫ t, density t*ψ K t ∂μ‖^2) =
      ∑ K ∈ rows, ‖∫ t, density t*(∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2 :=
    Finset.sum_coe_sort rows (fun K : Ideal Eis =>
      ‖∫ t, density t*(∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2)
  rw [hsum] at hh
  simp only [norm_mul,mul_pow,← Finset.mul_sum]
  simpa only [E,mul_assoc] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.SurvivingEnergy -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem surviving_physical_source_energy
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C₀ C : ℝ), 0≤C₀ ∧ 0<C ∧
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ)≤X)
      (D : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
        ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property).1 (S P.val)).generator N a c mode)
      (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis⧸(F.sum (S P)).ideal i)≠2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y) →
      (∀ b ∈ bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L) →
      (∀ K P hp, (D K P hp).fixedFactor=D0.fixedFactor) →
      (∀ K P hp u m n b, actualCuspColumn (D K P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
      (∀ K ∈ rows, ‖r₀ K‖≤1) → (∀ P ∈ Pset, ‖aw₀ P‖≤1) → (∀ n b, ‖w₀ n b‖≤1) →
      let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
      let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R
      let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
      (∑ K : rows, ‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      scalar^2*((branches.card:ℝ)*∑ e∈branches,
        let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
        let Bq := extractedDualScale (frozenExtracted F jF e 2) B
        (frozenBranchScale F jF e)^2*
          (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨C,hC,henergy⟩ := integrated_filtered_actual_reflected_energy
    (Ω := ℝ) (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode) ε hε
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsource⟩ := weighted_finite_physical_row_branch_measure
    (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode)
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW 0
  refine ⟨degree,C₀,C,hC₀,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
  let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R
  let density := twistedDensity U W θ R
  let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
  let r := fun t K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ)
  let aw := fun t P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ)
  let w := fun t n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)
  obtain ⟨hsource',hdi,_,hl1,_⟩ := hsource F s hc u m θ T QK QP Qn Qb hT hQK hQP hQn hQb
  have hpair (K : rows) (P : Pset) (hKP : IsCoprime K.val P.val) :
      Pairwise (Function.onFun IsCoprime (F.reflected K.val (hrows K.val K.property).1 (S P.val)).ideal) := by
    apply F.reflected_pairwise _ _ _ hF
    · intro i j hij
      change IsCoprime ((F.sum (S P.val)).ideal (Sum.inr i)) ((F.sum (S P.val)).ideal (Sum.inr j))
      exact hScop P.val P.property (Sum.inr_injective.ne hij)
    · rw [hproducts P.val P.property]
      exact hKP
    · exact (hrowcop K.val K.property).1
    · intro f i
      change IsCoprime ((F.sum (S P.val)).ideal (Sum.inl f)) ((F.sum (S P.val)).ideal (Sum.inr i))
      exact hScop P.val P.property (Sum.inl_ne_inr : (Sum.inl f : φ⊕σ)≠Sum.inr i)
  have hn0 : ∀ n ∈ nset, n≠0 := fun n hn' => (hn n hn').1.1.ne_zero
  have hb0 : ∀ b ∈ bset, b≠0 := by
    intro b hb' hbzero
    exact (hb b hb').1 (by rw [hbzero,primaryGenerator_zero])
  have hidentity (K : rows) :
      weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀ =
      (scalar:ℂ)*∫ t : ℝ, density t*∑ e∈branches,
        weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor (actualCuspColumn D0 s hc u m)
          (r t) (aw t) (w t) u m Pset nset bset K.val := by
    simpa only [sum_branches_eq_surviving] using hsource' K.val (hrows K.val K.property).1 S jF Pset nset bset (D K) hproducts hn0 hb0 r₀ aw₀ w₀
      G0 D0 (hpair K) (hκ K) (hA K) (fun b hb' => (hb b hb').1)
  have hh := henergy X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m rows nset bset Pset S branches volume density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdi
    (fun K hK => weightedKernelCoordinate_measurable windows M (r₀ K) 0 (-2) QK _)
    (fun P hP => weightedKernelCoordinate_measurable windows M (aw₀ P) 1 (-2) QP _)
    (fun n hn b hb => weightedKernelDual_measurable windows M (w₀ n b) Qn Qb _ _)
    (fun t K hK => weightedKernelCoordinate_norm windows M hwindowNorm hwindows _ (hr₀ K hK) _ _ _ _ _)
    (fun t P hP => weightedKernelCoordinate_norm windows M hwindowNorm hwindows _ (haw₀ P hP) _ _ _ _ _)
    (fun t n b => weightedKernelDual_norm windows M hwindowNorm hwindows _ (hw₀ n b) _ _ _ _ _)
  have hR : 0<R := by
    have hCC := actualKernelCoefficient_pos F s hc m T hT
    dsimp only [R,kernelCenter]
    positivity
  have hscalar : 0<scalar := by
    have hr := ramifiedScale_pos 1 completedRamifiedStep (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) m
    have hs := smallScalar_pos hR
    dsimp only [scalar]
    positivity
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hscalar] at hh
  have hl1' : (∫ t : ℝ, ‖density t‖)≤C₀*(1+‖θ‖)^degree := by
    simpa only [pow_zero,one_mul] using hl1
  have hsquare : (∫ t : ℝ, ‖density t‖)^2≤(C₀*(1+‖θ‖)^degree)^2 :=
    (sq_le_sq₀ (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)).mpr hl1'
  simp_rw [hidentity]
  rw [Finset.sum_coe_sort rows (fun K : Ideal Eis => ‖(scalar:ℂ)*∫ t : ℝ, density t*∑ e∈branches,
    weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor (actualCuspColumn D0 s hc u m)
      (r t) (aw t) (w t) u m Pset nset bset K‖^2)]
  apply hh.trans
  apply mul_le_mul_of_nonneg_left hsquare
  apply mul_nonneg (sq_nonneg _)
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro e he
  have hYq : 0≤extractedDualScale (frozenExtracted F jF e 1) Y := le_trans zero_le_one (le_max_left _ _)
  have hBq : 0≤extractedDualScale (frozenExtracted F jF e 2) B := le_trans zero_le_one (le_max_left _ _)
  positivity

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.AnnularNormalization -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

lemma reciprocal_annulus_normalization (r Qn Qb kn kb : ℝ)
    (hr : 0< r) (hn : 0<Qn) (hb : 0<Qb) (hkn : 0<kn) (hkb : 0<kb) :
    1/(r*Real.sqrt Qn*Qb) = Real.sqrt kn*kb/(r*Real.sqrt (kn*Qn)*(kb*Qb)) := by
  rw [Real.sqrt_mul hkn.le]
  have hs : Real.sqrt kn≠0 := (Real.sqrt_pos.mpr hkn).ne'
  field_simp

theorem physical_scalar_extracted (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r Qn Qb kn kb R A : ℝ)
    (hr : 0< r) (hn : 0<Qn) (hb : 0<Qb) (hkn : 0<kn) (hkb : 0<kb) :
    A/(r*Real.sqrt Qn*Qb)*smallScalar R =
      (A*Real.sqrt kn*kb)*extractedOutsideScalar F jF e r
        (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))
        (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)) R := by
  have hp (v : Fin 3) : (Ideal.absNorm (frozenExtracted F jF e v):ℝ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v)
  unfold extractedOutsideScalar
  rw [mul_div_cancel₀ _ (hp 1),mul_div_cancel₀ _ (hp 2)]
  have h := reciprocal_annulus_normalization r Qn Qb kn kb hr hn hb hkn hkb
  calc
    _ = A*(1/(r*Real.sqrt Qn*Qb))*smallScalar R := by ring
    _ = _ := by rw [h]; ring

theorem annular_kernel_threshold (Z T tau C r QK QP Qn Qb kn kb D1 D2 : ℝ)
    (hT : 0<T) (htau : 0<tau) (hC : 0<C) (hr : 0< r)
    (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkn : 0<kn) (hkb : 0<kb) (h1 : 0<D1) (h2 : 0<D2) :
    Real.logb Z (kn*Qn/D1)+3*Real.logb Z (kb*Qb/D2)+3*Real.logb Z r-
      Real.logb Z (kernelCenter (T/(27*tau^2*C^2)*r^3) QK QP Qn Qb) =
    Real.logb Z (27*tau^2*C^2*QK^2*QP^2*kn*kb^3/(T*D1*D2^3)) := by
  have hR : 0<kernelCenter (T/(27*tau^2*C^2)*r^3) QK QP Qn Qb := by
    unfold kernelCenter
    positivity
  have hv : 0<kn*Qn/D1 := by positivity
  have hl : 0<kb*Qb/D2 := by positivity
  have heq : (kn*Qn/D1)*(kb*Qb/D2)^3*r^3 /
      kernelCenter (T/(27*tau^2*C^2)*r^3) QK QP Qn Qb =
      27*tau^2*C^2*QK^2*QP^2*kn*kb^3/(T*D1*D2^3) := by
    unfold kernelCenter
    field_simp
  rw [← heq,Real.logb_div (by positivity) hR.ne',
    Real.logb_mul (by positivity) (pow_ne_zero _ hr.ne'),
    Real.logb_mul hv.ne' (pow_ne_zero _ hl.ne'),Real.logb_pow,Real.logb_pow]
  norm_num

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.TerminalThreshold -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}

lemma frozenExtracted_eq_ideal (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (v : Fin 3) :
    frozenExtracted F jF e v = reflectionExtractedDivisor F.ideal jF e v := by
  simp only [frozenExtracted,PrimeFamily.generator_span]

theorem actual_kernel_terminal_threshold (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (m : ℕ) (Z T QK QP Qn Qb kn kb : ℝ)
    (hT : 0<T) (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkn : 0<kn) (hkb : 0<kb) :
    Real.logb Z (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))+
      3*Real.logb Z (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2))+
      3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)-
      Real.logb Z (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb) =
    InverseTerminalWidths.terminalDualWidth Z (Real.logb Z QK) (Real.logb Z QP) (Real.logb Z T)
      F.ideal jF e +
    Real.logb Z (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3) := by
  have hr : 0< ramifiedScale 1 completedRamifiedStep m := ramifiedScale_pos _ _
    (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) _
  have htau := sourceCuspScale_pos s.index
  have hp (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hcn := hp (Ideal.span {c}) (Ideal.span_singleton_eq_bot.not.mpr hc)
  have hfn := hp (∏ i, F.ideal i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (F.ideal i)))
  have hd (v : Fin 3) := hp (frozenExtracted F jF e v) (frozenExtracted_ne_zero F jF e v)
  have hcc : actualKernelCoefficient F s m T =
      T/(27*(sourceCuspScale s.index)^2*
        ((Ideal.absNorm (Ideal.span {c}):ℝ)*(Ideal.absNorm (∏ i,F.ideal i):ℝ))^2)*
      (ramifiedScale 1 completedRamifiedStep m)^3 := by
    simp only [actualKernelCoefficient,fixedKernelCoefficient,map_one,Nat.cast_one,one_pow,mul_one,map_mul,Nat.cast_mul]
  rw [hcc,annular_kernel_threshold Z T (sourceCuspScale s.index)
    ((Ideal.absNorm (Ideal.span {c}):ℝ)*(Ideal.absNorm (∏ i,F.ideal i):ℝ))
    _ QK QP Qn Qb kn kb _ _ hT htau (mul_pos hcn hfn) hr hK hP hn hb hkn hkb (hd 1) (hd 2)]
  unfold InverseTerminalWidths.terminalDualWidth InverseTerminalWidths.normWidth
  rw [← frozenExtracted_eq_ideal F jF e 1,← frozenExtracted_eq_ideal F jF e 2]
  have hd1 := hd 1
  have hd2 := hd 2
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow]
  norm_num only [Nat.cast_ofNat]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.ThresholdError -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open CompletedDyadic CompletedGauss
noncomputable section

lemma fixed_abs_log_threshold (C η : ℝ) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ Z : ℝ, Z₀≤Z → |Real.logb Z C|≤η := by
  obtain ⟨Z₀,hZ₀,h⟩ := InverseTerminalWidths.constant_log_error
    (Real.exp |Real.log C|) η (Real.exp_pos _) hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ
  have hz : 0<Real.log Z := Real.log_pos (lt_of_lt_of_le hZ₀ hZ)
  have hh := h Z hZ
  simpa only [Real.logb,Real.log_exp,abs_div,abs_of_pos hz] using hh

lemma reflectedExponent_threshold_error (O₀ H S₀ B₀ za v ell el Td err η : ℝ)
    (herr : |err|≤η) :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el (Td+err) ≤
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el Td+η/2 := by
  have hη : 0≤η := (abs_nonneg err).trans herr
  have he : -η≤err := (abs_le.mp herr).1
  have hh : max 0 (Td-v-3*ell-el) ≤ max 0 (Td+err-v-3*ell-el)+η := by
    apply max_le
    · linarith [le_max_left (0:ℝ) (Td+err-v-3*ell-el)]
    · linarith [le_max_right (0:ℝ) (Td+err-v-3*ell-el)]
  unfold InverseTerminalWidths.reflectedExponent
  linarith

theorem literal_threshold_error_uniform (C η : ℝ) (hC : 0<C) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ Z : ℝ, Z₀≤Z → ∀ (m : ℕ) (O₀ H S₀ B₀ za v ell Td : ℝ),
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)) (Td+Real.logb Z C) ≤
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
        (InverseTerminalWidths.ramifiedWidth Z m) Td+η/2 := by
  obtain ⟨Z₀,hZ₀,herr⟩ := fixed_abs_log_threshold (C/81) η hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ m O₀ H S₀ B₀ za v ell Td
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hid : Td+Real.logb Z C-4*Real.logb Z 3=Td+Real.logb Z (C/81) := by
    rw [Real.logb_div hC.ne' (by norm_num)]
    have hp := Real.logb_pow Z 3 4
    norm_num at hp
    linarith
  have hh := literal_reflectedExponent_le_signed Z hz m O₀ H S₀ B₀ za v ell (Td+Real.logb Z C)
  rw [hid] at hh
  exact hh.trans (reflectedExponent_threshold_error O₀ H S₀ B₀ za v ell
    (InverseTerminalWidths.ramifiedWidth Z m) Td (Real.logb Z (C/81)) η (herr Z hZ))

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.AnnularExponent -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

theorem physical_scalar_hybrid_shape (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (Z r Qn Qb kn kb R A C X L ε : ℝ)
    (hZ : 1<Z) (hr : 0< r) (hn : 0<Qn) (hb : 0<Qb) (hkn : 0<kn) (hkb : 0<kb)
    (hR : 0<R) (hC : 0≤C) (hX : 0<X) (hL : 0<L) :
    let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
    let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
    (A/(r*Real.sqrt Qn*Qb)*smallScalar R)^2 * (frozenBranchScale F jF e)^2 *
      (C*(X*U*B*L)^ε*(X+U*B)*B*(U+L+(U*L)^(2/3:ℝ))) ≤
      (A*Real.sqrt kn*kb)^2*(6*C)*Z^(
        InverseTerminalWidths.reflectedExponent 0 (Real.logb Z X)
          (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
          (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
          (Real.logb Z L) (Real.logb Z U) (Real.logb Z B) (3*Real.logb Z r)
          (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R) +
        ε*(Real.logb Z X+Real.logb Z U+Real.logb Z B+Real.logb Z L)) := by
  let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
  let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
  have hp (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  have hU : 0<U := div_pos (mul_pos hkn hn) (hp 1)
  have hB : 0<B := div_pos (mul_pos hkb hb) (hp 2)
  have hs := physical_scalar_extracted F jF e r Qn Qb kn kb R A hr hn hb hkn hkb
  have he := extractedOutsideScalar_log_widths F jF e Z r U B R hZ hr hU hB hR
  have hz0 : 0<Z := lt_trans zero_lt_one hZ
  have hpow (Q : ℝ) (hQ : 0<Q) : Z^(Real.logb Z Q)=Q := Real.rpow_logb hz0 (ne_of_gt hZ) hQ
  have hh := normalized_hybrid_shape hZ.le (Real.logb Z X) (Real.logb Z U) (Real.logb Z B)
    (3*Real.logb Z r) (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
    (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
    (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R) (Real.logb Z L) ε
  rw [hpow X hX,hpow U hU,hpow B hB,hpow L hL,← he] at hh
  have hbnd := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hC)
    (sq_nonneg (A*Real.sqrt kn*kb))
  dsimp only
  rw [hs]
  convert hbnd using 1 <;> ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.TruncatedSource -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def retainedDyads (scale B : ℝ) : Finset (ℕ×ℕ×ℕ) :=
  (retainedDyadicBox scale B).filter (fun i => rawDyadicCenter scale i≤B)

lemma mem_retainedDyads (scale B : ℝ) (hs : 0<scale) (i : ℕ×ℕ×ℕ) :
    i∈retainedDyads scale B ↔ rawDyadicCenter scale i≤B := by
  simp only [retainedDyads,Finset.mem_filter]
  exact ⟨And.right,fun hi => ⟨center_mem_retainedDyadicBox scale B hs i hi,hi⟩⟩

lemma retainedDyads_card_le (scale B : ℝ) :
    (retainedDyads scale B).card≤(retainedDyadicBox scale B).card := Finset.card_filter_le _ _

lemma literalDyadicBlock_summable (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) (u : Eisˣ) :
    Summable (literalDyadicBlock G D s hc j S W X u) := by
  have hs := ((literalRawSeries_summable_norm G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm).prod_factor u
  have hh := (dualDyadicIndexEquiv.symm.summable_iff.mpr hs).sigma
  apply hh.congr
  intro i
  simp only [tsum_fintype,Fintype.sum_prod_type,literalDyadicBlock,Function.comp_apply]
  rfl

lemma tsum_sub_finset_eq_tail {α : Type*} (f : α→ℂ) (hf : Summable f) (A : Finset α) :
    (∑' i,f i)-(∑ i∈A,f i)=∑' i,if i∉A then f i else 0 := by
  have hh := hf.sum_add_tsum_subtype_compl A
  have ht : (∑' x : {x // x∉A}, f x.val)=∑' i,if i∉A then f i else 0 := by
    calc
      _ = ∑' x, ({x | x∉A} : Set α).indicator f x := tsum_subtype {x | x∉A} f
      _ = _ := by
        apply tsum_congr
        intro i
        by_cases hi : i∈A <;> simp [hi]
  rw [ht] at hh
  exact eq_sub_of_add_eq' hh |>.symm

theorem actual_truncated_dyadic_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (θ X T : ℝ), 0<X → 0<T →
      ‖(∑' i,literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i)-
        (∑ i∈retainedDyads (literalRawScale G s X) (16*T),
          literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i)‖≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by
  obtain ⟨degree,C,hC,hbound⟩ := literal_dyadic_tail_uniform_height (ι:=ι) (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro G D s hc hN hbase hchar j hj S u θ X T hX hT
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hs := literalDyadicBlock_summable G D s hc hN hbase hchar j hj S
    (CompletedHeight.normTwistedSource W θ) lo hi hlo
    ((CompletedHeight.normTwistedSource_support W θ).trans hWs) htw X hX u
  rw [tsum_sub_finset_eq_tail _ hs]
  have hb := hbound G D s hc hN hbase hchar j hj S u θ X T hX hT
    (fun i => i∉retainedDyads (literalRawScale G s X) (16*T))
    (fun i hi => (lt_of_not_ge (fun h => hi ((mem_retainedDyads _ _ (literalRawScale_pos G s hc X hX) i).mpr h))).le)
  apply le_trans ?_ hb
  apply le_of_eq
  congr 1
  apply tsum_congr
  intro i
  by_cases hi : i∈retainedDyads (literalRawScale G s X) (16*T) <;> simp [hi]
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.UniformMeasure -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v w
variable {N a c : Eis} {mode : Bool}

theorem actual_reflected_finite_source_uniform_type_uniform
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ {κ : Type w} (source : Finset κ) (weight : κ→ℂ)
        (K : κ→Ideal Eis) (hK : ∀ j, Admissible (K j)) (S : κ→PrimeFamily σ) (jF : φ→ℕ)
        (D : ∀ j, ControlledStratumArithmetic (F.reflected (K j) (hK j) (S j)).generator N a c mode)
        (n b : κ→Ideal Eis), (∀ j ∈ source, n j≠0 ∧ b j≠0) →
        (∑ j ∈ source, weight j*actualKernelSourceTerm F (K j) (hK j) (S j) jF (D j) s hc
          unit m (n j) (b j) windows QK QP Qn Qb W θ X) =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            ∑ j ∈ source, (weight j*actualMixedCoefficient F (K j) (hK j) (S j) jF (D j) s hc unit m (n j) (b j))*
              (kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm (K j):ℝ)*
                kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm (∏ i, (S j).ideal i):ℝ)*
                kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm (n j):ℝ) (Ideal.absNorm (b j):ℝ))) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := reflected_finite_source_uniform.{w}
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro φ σ _ _ F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  have hr := ramifiedScale_pos 1 completedRamifiedStep (by norm_num)
    (lt_trans zero_lt_one completedRamifiedStep_gt_one) m
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep θ (actualKernelCoefficient F s m X) QK QP Qn Qb
    (ramifiedScale 1 completedRamifiedStep m) (actualKernelCoefficient_pos F s hc m X hX)
    hQK hQP hQn hQb hr
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro κ source weight K hK S jF D n b hn
  have hnorm (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hpos (j : κ) (hj : j ∈ source) : (0:ℝ)<Ideal.absNorm (K j) ∧
      (0:ℝ)<Ideal.absNorm (∏ i, (S j).ideal i) ∧ (0:ℝ)<Ideal.absNorm (n j) ∧ (0:ℝ)<Ideal.absNorm (b j) :=
    ⟨hnorm _ (hK j).1,hnorm _ (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne ((S j).ideal i))),
      hnorm _ (hn j hj).1,hnorm _ (hn j hj).2⟩
  have hh := he source (fun j => weight j*actualMixedCoefficient F (K j) (hK j) (S j) jF (D j) s hc unit m (n j) (b j))
    (fun j => (Ideal.absNorm (K j):ℝ)) (fun j => (Ideal.absNorm (∏ i, (S j).ideal i):ℝ))
    (fun j => (Ideal.absNorm (n j):ℝ)) (fun j => (Ideal.absNorm (b j):ℝ)) hpos
  simpa only [actualKernelSourceTerm_numeric,mul_assoc] using hh

theorem weighted_finite_physical_row_common_measure_type_uniform
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ)
        (Pset nset bset : Finset (Ideal Eis))
        (D : ∀ P : Pset, IsCoprime K P.val →
          ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode),
        (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) → (∀ n ∈ nset, n≠0) → (∀ b ∈ bset, b≠0) →
        ∀ (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
        weightedFinitePhysicalKernelRow F K hK S jF Pset nset bset D s hc unit m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc
              (fun K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ))
              (fun P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ))
              (fun n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)) unit m) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := actual_reflected_finite_source_uniform_type_uniform
    (N := N) (a := a) (c := c) (mode := mode)
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro φ σ _ _ F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep (φ:=φ) (σ:=σ) F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀
  let T := CoprimeSourceIndex K Pset nset bset
  have hh := he (Finset.univ : Finset T) (fun x => r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val) (fun _ => K) (fun _ => hK)
    (fun x => S x.1.val.val) jF (fun x => D x.1.val x.1.property)
    (fun x => x.2.1.val) (fun x => x.2.2.val)
    (fun x _ => ⟨hn _ x.2.1.property,hb _ x.2.2.property⟩)
  unfold weightedFinitePhysicalKernelRow
  rw [hh]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [T]
  congr 1
  rw [weightedPhysicalReflectedRow_eq_coprime_source]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hprod x.1.val.val x.1.val.property]
  ring

theorem weighted_finite_physical_row_branch_measure_type_uniform
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ)
        (Pset nset bset : Finset (Ideal Eis))
        (D : ∀ P : Pset, IsCoprime K P.val →
          ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode),
        (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) → (∀ n ∈ nset, n≠0) → (∀ b ∈ bset, b≠0) →
        ∀ (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
        ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
          (D0 : ControlledStratumArithmetic G0.generator N a c mode),
        (∀ P : Pset, IsCoprime K P.val → Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal)) →
        (∀ P hp, (D P hp).fixedFactor=D0.fixedFactor) →
        (∀ P hp u m n b, actualCuspColumn (D P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
        (∀ b ∈ bset, primaryGenerator b≠0) →
        weightedFinitePhysicalKernelRow F K hK S jF Pset nset bset D s hc unit m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
              (actualCuspColumn D0 s hc unit m)
              (fun K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ))
              (fun P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ))
              (fun n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)) unit m Pset nset bset K)) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := weighted_finite_physical_row_common_measure_type_uniform
    (N := N) (a := a) (c := c) (mode := mode)
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro φ σ _ _ F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep (φ:=φ) (σ:=σ) F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀ ι _ G0 D0 hcop hκ hA hbgen
  rw [he K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  exact weightedPhysicalReflectedRow_eq_branches F K hK S jF Pset nset bset hprod D hcop
    G0 D0 s hc hκ hA hbgen _ _ _ unit m

end
end SevenEighths.InverseReflectedPhase

end OAI

end

