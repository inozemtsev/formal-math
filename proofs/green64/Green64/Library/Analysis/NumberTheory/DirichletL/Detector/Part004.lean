module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part021

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Detector / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianTailBudget -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianWeightedMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k R : ℝ) : ℝ := R^k*gaussianJointMoment V hV J R

lemma gaussianWeightedMoment_nonneg (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k R : ℝ) (hR : 0≤R) : 0≤gaussianWeightedMoment V hV J k R := by
  unfold gaussianWeightedMoment
  exact mul_nonneg (Real.rpow_nonneg hR _) (gaussianJointMoment_nonneg V hV J R)

lemma gaussianWeightedMoment_power_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k A : ℝ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→ gaussianWeightedMoment V hV J k R≤C*R^(-A) := by
  obtain ⟨C,hC,hb⟩ := gaussianJointMoment_power_bound V hV J (A+k)
  refine ⟨C,hC,?_⟩
  intro R hR
  have hh := mul_le_mul_of_nonneg_left (hb R hR) (Real.rpow_nonneg hR.le k)
  change R^k*gaussianJointMoment V hV J R≤_
  calc
    _ ≤ R^k*(C*R^(-(A+k))) := hh
    _ = C*R^(-A) := by
      rw [←mul_assoc,mul_comm (R^k) C,mul_assoc,←Real.rpow_add hR]
      congr 2
      ring

lemma gaussianWeightedMoment_polynomial_decay (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (k : ℝ) (N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→ gaussianWeightedMoment V hV J k R≤C/(1+R)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianWeightedMoment_power_bound V hV J k 0
  obtain ⟨C,hC,hdecay⟩ := gaussianWeightedMoment_power_bound V hV J k (N:ℝ)
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro R hR
  have hden : 0<(1+R)^N := pow_pos (by linarith) _
  by_cases hr1 : R≤1
  · have hh := hzero R hR
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay R hR
    rw [Real.rpow_neg hR.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2*R)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hm := mul_le_mul_of_nonneg_left hp (show 0≤C*(R^N)⁻¹ by positivity)
    rw [mul_pow] at hm
    have hn : R^N≠0 := ne_of_gt (pow_pos hR _)
    have he : (C*(R^N)⁻¹)*((2:ℝ)^N*R^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

theorem gaussianWeightedMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (k s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z))≤C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianWeightedMoment_polynomial_decay V hV J k N
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound ((2:ℝ)^j/Z) (div_pos (by positivity) hZ))
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z) :=
    mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s) (gaussianWeightedMoment_nonneg V hV J k _ (by positivity))
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

def gaussianRemoteMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (s Z A : ℝ) (j : ℕ) : ℝ :=
  if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
    ((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)
  else 0

theorem gaussianRemoteMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J N : ℕ) (s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀Z A : ℝ,0<Z→1≤A→
      Summable (gaussianRemoteMoment V hV J s Z A) ∧
      (∑'j : ℕ,gaussianRemoteMoment V hV J s Z A j)≤C*Z^s/A^N := by
  obtain ⟨Cm,hCm,hm⟩ := gaussianWeightedMoment_summed V hV J (-(N:ℝ)) s hs
  obtain ⟨Cp,hCp,hp⟩ := gaussianWeightedMoment_summed V hV J (N:ℝ) s hs
  refine ⟨Cm+Cp,by positivity,?_⟩
  intro Z A hZ hA
  have hAp : 0<A := lt_of_lt_of_le zero_lt_one hA
  have hAN : 0<A^N := pow_pos hAp N
  obtain ⟨hsm,htm⟩ := hm Z hZ
  obtain ⟨hsp,htp⟩ := hp Z hZ
  let U : ℕ→ℝ := fun j=>
    (((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (-(N:ℝ)) ((2:ℝ)^j/Z)+
      ((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (N:ℝ) ((2:ℝ)^j/Z))/A^N
  have hU : Summable U := (hsm.add hsp).div_const _
  have hnon (j : ℕ) : 0≤gaussianRemoteMoment V hV J s Z A j := by
    unfold gaussianRemoteMoment
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianJointMoment_nonneg V hV J _)
    · rfl
  have hb (j : ℕ) : gaussianRemoteMoment V hV J s Z A j≤U j := by
    let R := (2:ℝ)^j/Z
    have hR : 0<R := div_pos (by positivity) hZ
    have hM : 0≤gaussianJointMoment V hV J R := gaussianJointMoment_nonneg V hV J R
    unfold gaussianRemoteMoment
    split_ifs with hj
    · have he : A^N≤R^(-(N:ℝ))+R^(N:ℝ) := by
        rcases hj with hlo|hhi
        · have hra : R*A≤1 := (le_div_iff₀ hAp).mp (by simpa only [one_div,R] using hlo)
          have hh := pow_le_pow_left₀ (by positivity : 0≤R*A) hra N
          rw [mul_pow,one_pow] at hh
          have hi : A^N≤R^(-(N:ℝ)) := by
            rw [Real.rpow_neg hR.le,Real.rpow_natCast]
            rw [←one_div]
            exact (le_div_iff₀ (pow_pos hR N)).mpr (by simpa only [mul_comm] using hh)
          exact hi.trans (le_add_of_nonneg_right (Real.rpow_nonneg hR.le _))
        · have hi : A^N≤R^(N:ℝ) := by
            rw [Real.rpow_natCast]
            exact pow_le_pow_left₀ hAp.le hhi N
          exact hi.trans (le_add_of_nonneg_left (Real.rpow_nonneg hR.le _))
      change ((2:ℝ)^j)^s*gaussianJointMoment V hV J R≤_
      dsimp only [U]
      apply (le_div_iff₀ hAN).mpr
      calc
        _ ≤ (((2:ℝ)^j)^s*gaussianJointMoment V hV J R)*(R^(-(N:ℝ))+R^(N:ℝ)) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg (by positivity) _) hM)
        _ = _ := by unfold gaussianWeightedMoment;dsimp only [R];ring
    · dsimp only [U]
      apply div_nonneg _ hAN.le
      exact add_nonneg
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianWeightedMoment_nonneg V hV J _ _ hR.le))
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianWeightedMoment_nonneg V hV J _ _ hR.le))
  have hsum := Summable.of_nonneg_of_le hnon hb hU
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,U j := hsum.tsum_le_tsum hb hU
    _ = ((∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (-(N:ℝ)) ((2:ℝ)^j/Z))+
        (∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (N:ℝ) ((2:ℝ)^j/Z)))/A^N := by
      dsimp only [U]
      rw [tsum_div_const,hsm.tsum_add hsp]
    _ ≤ (Cm*Z^s+Cp*Z^s)/A^N := div_le_div_of_nonneg_right (add_le_add htm htp) hAN.le
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianRemoteRows -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss FourierBridge
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianCompletedFamilyIntegral {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) : ℂ :=
  ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
    (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
    (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t

def gaussianCompletedFamilyMass {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*∏i,‖W i (q k i)‖

lemma gaussianCompletedFamilyMass_nonneg {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (W : ι→ℝ→ℂ) (q : α→ι→ℝ) :
    0≤gaussianCompletedFamilyMass F a W q := by
  unfold gaussianCompletedFamilyMass
  positivity

lemma gaussianCompletedFamily_integrable {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) (hT : 0<T) :
    Integrable (fun t : ℝ=>(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
      (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t) := by
  have hh := integrable_finsetSum F (fun k _=>(gaussian_selected_completed_integrable W (q k)
    (gaussianJointDensity V hV (T/Z)) S (D k) (Ψ k) T hT).const_mul (a k))
  simpa only [Finset.sum_mul,mul_assoc] using hh

theorem gaussianCompletedFamily_crude :
    ∃C : ℝ,0<C ∧ ∀{α ι : Type*} [Fintype ι],∀F : Finset α,∀a : α→ℂ,
      ∀S : Finset Id,∀D : α→Id,∀Ψ : α→O→*ℂ,
      (∀k∈F,∀n,‖Ψ k n‖≤1)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀V : SchwartzMap ℝ ℂ,∀hV : HasCompactSupport (V:ℝ→ℂ),∀T Z : ℝ,0<T→
      ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV T Z‖≤
        C*T^2*gaussianCompletedFamilyMass F a W q*gaussianJointMoment V hV 0 (T/Z) := by
  obtain ⟨C,hC,hb⟩ := gaussianFixedWindow_completed_crude
  refine ⟨C,hC,?_⟩
  intro α ι _ F a S D Ψ hΨ W q V hV T Z hT
  have hf := gaussianCompletedFamily_integrable F a S D Ψ W q V hV T Z hT
  have hp (t : ℝ) :
      ‖(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t‖≤
      (C*T^2*gaussianCompletedFamilyMass F a W q)*‖gaussianJointDensity V hV (T/Z) t‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ∑k∈F,‖a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i)))‖ := norm_sum_le _ _
      _ ≤ ∑k∈F,‖a k‖*(C*T^2)*(∏i,‖W i (q k i)‖) := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [norm_mul,norm_prod,logPhase_norm,mul_one]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hb S (D k) (Ψ k) (hΨ k hk) T t hT) (norm_nonneg _))
          (Finset.prod_nonneg (fun _ _=>norm_nonneg _))
      _ = _ := by unfold gaussianCompletedFamilyMass;rw [Finset.mul_sum];congr 1;funext k;ring
  calc
    _ ≤ ∫t : ℝ,‖(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫t : ℝ,(C*T^2*gaussianCompletedFamilyMass F a W q)*‖gaussianJointDensity V hV (T/Z) t‖ :=
      integral_mono hf.norm ((gaussianJointDensity V hV (T/Z)).integrable.norm.const_mul _) hp
    _ = _ := by simp only [integral_const_mul,gaussianJointMoment,pow_zero,one_mul]

theorem gaussianCompletedFamily_remote (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{α ι : Type*} [Fintype ι],∀F : Finset α,∀a : α→ℂ,
      ∀S : Finset Id,∀D : α→Id,∀Ψ : α→O→*ℂ,
      (∀k∈F,∀n,‖Ψ k n‖≤1)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          C*gaussianCompletedFamilyMass F a W q*Z^2/A^N := by
  obtain ⟨Cr,hCr,hr⟩ := gaussianCompletedFamily_crude
  obtain ⟨Cg,hCg,hg⟩ := gaussianRemoteMoment_summed V hV 0 N 2 (by norm_num)
  refine ⟨Cr*Cg,by positivity,?_⟩
  intro α ι _ F a S D Ψ hΨ W q Z A hZ hA
  obtain ⟨hs,ht⟩ := hg Z A hZ hA
  let M := gaussianCompletedFamilyMass F a W q
  have hM : 0≤M := gaussianCompletedFamilyMass_nonneg F a W q
  have hb (j : ℕ) :
      (if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0)≤
      (Cr*M)*gaussianRemoteMoment V hV 0 2 Z A j := by
    unfold gaussianRemoteMoment
    split_ifs
    · simpa only [M,Real.rpow_two,mul_assoc,mul_comm,mul_left_comm] using
        hr F a S D Ψ hΨ W q V hV ((2:ℝ)^j) Z (by positivity)
    · simp
  have hnon (j : ℕ) : 0≤(if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
      ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0) := by split_ifs <;> positivity
  have hsum := Summable.of_nonneg_of_le hnon hb (hs.mul_left (Cr*M))
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,(Cr*M)*gaussianRemoteMoment V hV 0 2 Z A j := hsum.tsum_le_tsum hb (hs.mul_left (Cr*M))
    _ = (Cr*M)*∑'j : ℕ,gaussianRemoteMoment V hV 0 2 Z A j := tsum_mul_left
    _ ≤ (Cr*M)*(Cg*Z^(2:ℝ)/A^N) := mul_le_mul_of_nonneg_left ht (mul_nonneg hCr.le hM)
    _ = _ := by rw [Real.rpow_two];dsimp only [M];ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SpectralSeparation -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O

def baseRowCoefficient (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O →* ℂ :=
  targetMonoid η * InitialMeanSquare.conjugateMonoid Xi * reciprocityPhaseMonoid s hs

lemma spectralSummand_mul_fixed_twist (S : Finset (Ideal O)) (D I J : Ideal O)
    (φ Ψ : O →* ℂ) (t : ℂ) :
    spectralSummand S D (φ*Ψ) t I J =
      φ (completedIndex I J) * spectralSummand S D Ψ t I J := by
  have hc (η : O →* ℂ) : cubeWeight η J =
      star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3 *
        η (primaryGenerator J)^3 / (Ideal.absNorm J:ℂ) := rfl
  unfold spectralSummand
  rw [hc, hc]
  simp only [columnWeight, MonoidHom.mul_apply, map_mul, map_pow, mul_pow, completedIndex]
  ring

theorem spectralSummand_row_separation (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (Xi : O →* ℂ) (s : O)
    (hs : Supported (Ideal.span {s})) (m : O) (t : ℂ) :
    spectralSummand S D (rowCoefficient η Xi s hs m) t I J =
      idealRowHom m (Ideal.span {completedIndex I J}) *
        spectralSummand S D (baseRowCoefficient η Xi s hs) t I J := by
  have hr : rowCoefficient η Xi s hs m =
      ((idealRowHom m).toMonoidHom.comp principalIdealHom.toMonoidHom) *
        baseRowCoefficient η Xi s hs := by
    change _ * _ = _ * _
    exact mul_comm _ _
  rw [hr, spectralSummand_mul_fixed_twist]
  rfl

theorem calibrated_spectralSummand_separation (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : ProbePhysical.CalibrationData) (s : O)
    (hs : Supported (Ideal.span {s})) (m : O) (t : ℂ) :
    C.residueMonoid m * spectralSummand S D (rowCoefficient η C.Xi s hs m) t I J =
      ProbePhysical.calibratedNumerator C (completedIndex I J) m *
        spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J := by
  rw [spectralSummand_row_separation]
  unfold ProbePhysical.calibratedNumerator
  ring

theorem spectralSummand_zero_completedIndex (S : Finset (Ideal O)) (D I J : Ideal O)
    (Ψ : O →* ℂ) (t : ℂ) (hz : completedIndex I J=0) :
    spectralSummand S D Ψ t I J=0 := by
  rcases mul_eq_zero.mp hz with hI | hJ
  · have hg : squarefreeGaussCoefficient I=0 := by
      unfold squarefreeGaussCoefficient
      rw [dite_eq_right (by simp [hI])]
    simp only [spectralSummand, columnWeight, hg, zero_mul, zero_div, mul_zero]
  · have hJ' : primaryGenerator J=0 := (pow_eq_zero_iff (by decide : 3≠0)).mp hJ
    have hc : cubeWeight Ψ J=0 := by
      change star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3 *
        Ψ (primaryGenerator J)^3 / (Ideal.absNorm J:ℂ)=0
      simp [hJ', FiniteGaussPhase.angularFactor]
    simp only [spectralSummand, hc, mul_zero, zero_mul]

end SevenEighths.ProbeRow
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SpectralWeights -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma signed_diagonal_phase (omega : ℂ) (ho : omega^2=1) (e l k : ℕ) :
    omega^(((e+3*l)*k:ℕ):ℤ) * omega^(-((e*l+l.choose 2:ℕ):ℤ)) =
      omega^((e+3*l)*k+e*l+l.choose 2) := by
  have hn : omega≠0 := by intro h; simp [h] at ho
  have hi : omega⁻¹=omega := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using ho
  rw [zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, hi, ← pow_add]
  congr 1
  omega

lemma source_signed_phase (C omega : ℂ) (ho : omega^2=1) (e l k : ℕ) :
    C^l * omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ)) =
      localCubePhase C omega e l k := by
  have hn : omega≠0 := by intro h; simp [h] at ho
  rw [sub_eq_add_neg, zpow_add₀ hn, signed_diagonal_phase omega ho]
  rfl

lemma spectral_power_split (Q : ℝ) (hQ : 0<Q) (x w z : ℂ) (e l k m : ℕ) :
    (Q:ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
      ((Q:ℂ)^(-x)/(Q:ℂ)^(1/2:ℂ))^e *
      (((Q:ℂ)^(-x))^3/(Q:ℂ))^l * ((Q:ℂ)^(-w))^k * ((Q:ℂ)^(-6*z))^m := by
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  have h1 : (Q:ℂ)^(-x)/(Q:ℂ)^(1/2:ℂ) = (Q:ℂ)^(-x-(1/2:ℂ)) :=
    (Complex.cpow_sub _ _ hn).symm
  have h3 : ((Q:ℂ)^(-x))^3/(Q:ℂ) = (Q:ℂ)^(-1-3*x) := by
    rw [← Complex.cpow_nat_mul (Q:ℂ) 3 (-x)]
    calc
      _ = (Q:ℂ)^(3*(-x)) / (Q:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]; norm_num
      _ = (Q:ℂ)^(3*(-x)-1) := (Complex.cpow_sub _ _ hn).symm
      _ = _ := by congr 1; ring
  rw [h1, h3, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
  congr 1
  ring

lemma cpow_half_eq_sqrt (Q : ℝ) (hQ : 0≤Q) :
    (Q:ℂ)^(1/2:ℂ) = (Real.sqrt Q:ℂ) := by
  rw [Real.sqrt_eq_rpow]
  simpa using (Complex.ofReal_cpow hQ (1/2:ℝ)).symm

def sourceWeightedScalar (Q : ℝ) (eta a gamma1 C omega x w z scalar : ℂ)
    (e l k m : ℕ) : ℂ :=
  (-1:ℂ)^e * gamma1^(-(e:ℤ)) * eta^e * (a*C)^l *
    omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ)) * scalar *
    (Q:ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ))

theorem sourceWeightedScalar_eq (Q : ℝ) (hQ : 0<Q)
    (eta a gamma1 G1 C omega x w z scalar : ℂ) (hG : G1=gamma1*(Real.sqrt Q:ℂ))
    (ho : omega^2=1) (e l k m : ℕ) :
    sourceWeightedScalar Q eta a gamma1 C omega x w z scalar e l k m =
      weightedScalar Q eta a G1 C omega ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w))
        ((Q:ℂ)^(-6*z)) scalar e l k m := by
  unfold sourceWeightedScalar weightedScalar
  rw [spectral_power_split Q hQ, cpow_half_eq_sqrt Q hQ.le]
  rw [zpow_neg, zpow_natCast]
  have hphase := source_signed_phase 1 omega ho e l k
  simp only [localCubePhase, one_pow, one_mul] at hphase
  unfold localCubePhase
  rw [hphase, mul_pow a C, hG]
  simp only [mul_pow, div_pow]

  ring

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma firstGauss_eq_gamma_sqrt (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda ∉ Ideal.span {p}) :
    primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 =
      localGamma p hp.ne_zero hg 1 *
        (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hs : (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hQ).ne'
  unfold localGamma
  rw [pow_one, ProbePhase.normalizedTraceGauss_eq_normalizedGauss]
  simp only [ProbeGauss.normalizedGauss, ← Nat.card_eq_fintype_card]
  change _ = (gaussSum _ _ / (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ)) * _
  rw [div_mul_cancel₀ _ hs]
  simp only [primeGauss, map_one, one_mul, tsum_fintype, gaussSum]

theorem sourceWeightedScalar_actual (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda ∉ Ideal.span {p})
    (eta a x w z scalar : ℂ) (e l k m : ℕ) :
    sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
      (actualSextic (Ideal.span {p}) hg (-1)) x w z scalar e l k m =
    weightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-6*z)) scalar e l k m := by
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  simpa only [Complex.ofReal_natCast] using
    sourceWeightedScalar_eq _ hQ eta a (localGamma p hp.ne_zero hg 1) _
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1))
      x w z scalar (firstGauss_eq_gamma_sqrt p hp hg)
      (actualSextic_neg_one_sq _ hg) e l k m

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PhysicalNorms -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma elementNorm_mul (a b : ActualEisensteinCubic.O) :
    elementNorm (a*b)=elementNorm a*elementNorm b := by
  simp only [elementNorm,←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

lemma elementNorm_pow (a : ActualEisensteinCubic.O) (n : ℕ) :
    elementNorm (a^n)=elementNorm a^n := by
  simp only [elementNorm,←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]

lemma physical_radial_argument (B A s H : ActualEisensteinCubic.O) (X : ℝ)
    (hB : elementNorm B≠0) (hs : elementNorm s≠0) :
    (elementNorm B*elementNorm s*X)*elementNorm H/elementNorm ((B*A)*s)=
      X*elementNorm H/elementNorm A := by
  simp only [elementNorm_mul]
  field_simp

lemma physical_poisson_prefactor (B A S X : ℝ) (hB : 0<B) (hA : 0<A) (hS : 0<S) (hX : 0<X) :
    (Real.sqrt (B*S*X):ℂ)⁻¹*(Real.sqrt S:ℂ)⁻¹*((B*S*X/(B*A):ℝ):ℂ)=
      (Real.sqrt X:ℂ)/(Real.sqrt B:ℂ)/(A:ℂ) := by
  have hBc : (B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hB.ne'
  have hAc : (A:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hSb : (Real.sqrt B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB).ne'
  have hSs : (Real.sqrt S:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hS).ne'
  have hSx : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  rw [Real.sqrt_mul (mul_pos hB hS).le,Real.sqrt_mul hB.le]
  simp only [Complex.ofReal_mul,Complex.ofReal_div]
  field_simp
  have hb : (Real.sqrt B:ℂ)^2=(B:ℂ) := by exact_mod_cast Real.sq_sqrt hB.le
  have hs : (Real.sqrt S:ℂ)^2=(S:ℂ) := by exact_mod_cast Real.sq_sqrt hS.le
  have hx : (Real.sqrt X:ℂ)^2=(X:ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  rw [hs,hx]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.MellinPowers -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ProbeEuler

lemma sourceNormPower_identity (I J H X : ℝ) (hI : 0<I) (hJ : 0<J) (hH : 0<H) (hX : 0<X)
    (t z : ℂ) :
    ((I*J^3:ℝ):ℂ)⁻¹*((X*H/(I*J^3):ℝ):ℂ)^(-z)*
      ((I:ℂ)^(-t)*(J:ℂ)^(-3*t)) /
      ((Real.sqrt I:ℂ)*(J:ℂ)) * (Real.sqrt X:ℂ) =
      (X:ℂ)^(1/2-z)*(H:ℂ)^(-z)*
        (I:ℂ)^(-(t+1-z)-1/2)*(J:ℂ)^(-(1+3*(t+1-z))) := by
  have hi : (I:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hI.ne'
  have hj : (J:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hJ.ne'
  have hh : (H:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hH.ne'
  have hx : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  rw [←cpow_half_eq_sqrt I hI.le,←cpow_half_eq_sqrt X hX.le]
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (mul_pos hX hH).le (mul_pos hI (pow_pos hJ 3)).le]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  rw [Complex.mul_cpow_ofReal_nonneg hX.le hH.le]
  have hmul : ((I:ℂ)*(J:ℂ)^3)^(-z)=(I:ℂ)^(-z)*((J:ℂ)^3)^(-z) := by
    simpa only [Complex.ofReal_pow] using Complex.mul_cpow_ofReal_nonneg hI.le (pow_pos hJ 3).le (-z)
  rw [hmul]
  have hp : ((J:ℂ)^3)^(-z)=(J:ℂ)^((3:ℂ)*(-z)) := by
    simpa only [Real.rpow_ofNat,Real.rpow_natCast,Complex.ofReal_pow,Complex.cpow_ofNat,Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hJ.le (3:ℝ) (-z)).symm
  rw [hp]
  rw [show (J:ℂ)^3=(J:ℂ)^(3:ℂ) by simp]
  have hir : (I:ℂ)=Complex.exp (Complex.log (I:ℂ)) := (Complex.exp_log hi).symm
  have hjr : (J:ℂ)=Complex.exp (Complex.log (J:ℂ)) := (Complex.exp_log hj).symm
  simp only [Complex.cpow_def_of_ne_zero hi,Complex.cpow_def_of_ne_zero hj,
    Complex.cpow_def_of_ne_zero hh,Complex.cpow_def_of_ne_zero hx,div_eq_mul_inv,
    mul_inv_rev,←Complex.exp_neg,←Complex.exp_add]
  rw [hir,hjr]
  simp only [←Complex.exp_neg,←Complex.exp_add]
  rw [Complex.exp_log hi,Complex.exp_log hj]
  congr 1
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.Windows -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem elementWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun m : O => W (elementNorm m / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (ShortDraftLatticeCount.rowNormBall M).finite_toSet.subset
  intro m hm
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  have hnorm : elementNorm m ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hm)
  unfold elementNorm at hnorm
  exact_mod_cast hnorm.trans hM.le

theorem idealWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (Ideal.finite_setOfPred_absNorm_le M).subset
  intro I hI
  have hnorm : (Ideal.absNorm I : ℝ) ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hI)
  exact_mod_cast hnorm.trans hM.le

theorem elementWindow_mul_summable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) (F : O → ℂ) :
    Summable (fun m : O => W (elementNorm m / R) * F m) := by
  apply summable_of_hasFiniteSupport
  apply (elementWindow_finite_support W hW R hR).subset
  intro m hm hzero
  exact hm (by simp only [hzero, zero_mul])

theorem idealWindow_mul_summable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) (F : Ideal O → ℂ) :
    Summable (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R) * F I) := by
  apply summable_of_hasFiniteSupport
  apply (idealWindow_finite_support W hW R hR).subset
  intro I hI hzero
  exact hI (by simp only [hzero, zero_mul])

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PhysicalReopen -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

lemma supportedElement_ne_zero (s : O) (hs : Supported (Ideal.span {s})) : s≠0 := by
  intro h
  apply hs.1
  simp [h]

lemma finite_support_tsum_comm {α β : Type*} (f : α → β → ℂ) (S : Finset α)
    (hz : ∀ a, a∉S → ∀ b, f a b=0) (hs : ∀ a∈S, Summable (f a)) :
    (∑' a, ∑' b, f a b) = ∑' b, ∑' a, f a b := by
  calc
    _ = ∑ a∈S, ∑' b, f a b := tsum_eq_sum (fun a ha => by simp only [hz a ha, tsum_zero])
    _ = ∑' b, ∑ a∈S, f a b := (Summable.tsum_finsetSum hs).symm
    _ = _ := by
      apply tsum_congr
      intro b
      exact (tsum_eq_sum (fun a ha => hz a ha b)).symm

theorem physical_spectral_reopen (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O)
    (hs : Supported (Ideal.span {s})) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (K : ℝ) (hK : 0<K) (t : ℂ) (ht : 1<t.re) :
    (∑' m : O, C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) *
      W (elementNorm m/K) * spectralRow S D (rowCoefficient η C.Xi s hs m) t) =
    ∑' p : Ideal O × Ideal O, spectralSummand S D (baseRowCoefficient η C.Xi s hs) t p.1 p.2 *
      ∑' m : O, calibratedNumerator C (completedIndex p.1 p.2) m *
        sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) := by
  let F (m : O) (p : Ideal O × Ideal O) : ℂ :=
    C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) *
      spectralSummand S D (rowCoefficient η C.Xi s hs m) t p.1 p.2
  have hfin := elementWindow_finite_support W hW K hK
  have hzero : ∀ m, m∉hfin.toFinset → ∀ p, F m p=0 := by
    intro m hm p
    have hz : W (elementNorm m/K)=0 := by simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hm
    simp only [F, hz, mul_zero, zero_mul]
  have hsum (m : O) : Summable (F m) :=
    (spectralRow_summable S D (rowCoefficient η C.Xi s hs m)
      (rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one s hs m) t ht).mul_left _
  have he := finite_support_tsum_comm F hfin.toFinset hzero (fun m _ => hsum m)
  calc
    _ = ∑' m : O, ∑' p : Ideal O × Ideal O, F m p := by
      simp only [F, spectralRow, tsum_mul_left]
    _ = ∑' p : Ideal O × Ideal O, ∑' m : O, F m p := he
    _ = _ := by
      apply tsum_congr
      intro p
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      unfold F
      rw [spectralSummand_row_separation]
      unfold calibratedNumerator
      ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PhysicalRows -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PhysicalRowIndex := {I : Id // Supported I}×O

def physicalRowMonoid (η : HeckeFamily.Character) (C : CalibrationData) (r : PhysicalRowIndex) : O→*ℂ :=
  rowCoefficient η C.Xi (primaryGenerator r.1.val)
    ((supported_span_primaryGenerator_iff r.1.val).mpr r.1.property) r.2

def physicalRowWeight (C : CalibrationData) (W0 W1 : ℝ→ℂ) (X Y : ℝ) (r : PhysicalRowIndex) : ℂ :=
  if ∀P∈C.excluded,¬P∣r.1.val then
    let a := primaryGenerator r.1.val
    let ha := supported_primaryGenerator_ne_zero r.1.val r.1.property
    let q : ℝ := Ideal.absNorm r.1.val
    (Y:ℂ)⁻¹*W1 (q/Y)*CanonicalRowCompletion.idealRowHom C.generator r.1.val/
      (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q*X):ℂ))*
      C.residueMonoid r.2*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-r.2)*
        W0 (elementNorm r.2/(elementNorm C.generator*q*X))
  else 0

lemma physicalRowMonoid_norm (η : HeckeFamily.Character) (C : CalibrationData)
    (r : PhysicalRowIndex) (n : O) : ‖physicalRowMonoid η C r n‖≤1 :=
  rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ r.2 n

lemma physicalRowWeight_outer_zero (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) (h : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)=0) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  unfold physicalRowWeight
  split_ifs <;> simp [h]

lemma physicalRowWeight_inner_zero (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex)
    (h : W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))=0) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  unfold physicalRowWeight
  split_ifs <;> simp [h]

lemma physicalRowScale_pos (C : CalibrationData) (X : ℝ) (hX : 0<X)
    (s : {I : Id // Supported I}) : 0<elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X := by
  have hc : 0<elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hs : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  positivity

theorem physicalRowWeight_finite_support (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    (Function.support (physicalRowWeight C W0 W1 X Y)).Finite := by
  have ho := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  apply Set.Finite.of_finite_fibers Prod.fst
  · apply ho.subset
    rintro s ⟨r,hr,rfl⟩
    exact fun hz=>hr (physicalRowWeight_outer_zero C W0 W1 X Y r hz)
  · intro s hs
    have hm := elementWindow_finite_support W0 hW0 _ (physicalRowScale_pos C X hX s)
    apply ((Set.finite_singleton s).prod hm).subset
    intro r hr
    have he : r.1=s := hr.2
    refine ⟨he,?_⟩
    intro hz
    apply hr.1
    apply physicalRowWeight_inner_zero C W0 W1 X Y r
    simpa only [he] using hz

lemma physicalRowWeight_mul_summable (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (F : PhysicalRowIndex→ℂ) :
    Summable (fun r=>physicalRowWeight C W0 W1 X Y r*F r) := by
  apply summable_of_hasFiniteSupport
  apply (physicalRowWeight_finite_support C W0 W1 hW0 hW1 X Y hX hY).subset
  intro r hr hz
  exact hr (by dsimp only; rw [hz,zero_mul])

theorem markedPhysicalProbe_eq_rows (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (physicalRowMonoid η C r) t) := by
  have hf := physicalRowWeight_mul_summable C W0 W1 hW0 hW1 X Y hX hY
    (fun r=>verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (physicalRowMonoid η C r) t))
  rw [hf.tsum_prod]
  unfold markedPhysicalProbe
  rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  by_cases hc : ∀P∈C.excluded,¬P∣s.val
  · simp only [physicalRowWeight,physicalRowMonoid]
    try dsimp only
    simp only [ite_eq_left hc]
    rw [←tsum_mul_left,←tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  · simp only [physicalRowWeight]
    try dsimp only
    simp only [ite_eq_right hc,zero_mul,mul_zero,tsum_zero]

theorem markedPhysicalProbe_eq_gaussian_rows (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        correctedCompletedT C.excluded D (physicalRowMonoid η C r) gaussianCompletedProfile Z := by
  rw [markedPhysicalProbe_eq_rows η C D W0 W1 hW0 hW1 X Y Z hX hY]
  apply tsum_congr
  intro r
  rw [spectralRow_eq_gaussianCompleted _ _ _ (physicalRowMonoid_norm η C r) 4 (by norm_num) Z hZ]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianPhysicalTuple -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalRows_common_finset {α : Type*} (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (X Y : α→ℝ) (hX : ∀k∈F,0<X k) (hY : ∀k∈F,0<Y k) :
    ∃R : Finset PhysicalRowIndex,∀k∈F,∀r,r∉R→physicalRowWeight C W0 W1 (X k) (Y k) r=0 := by
  have hf (k : {k // k∈F}) := physicalRowWeight_finite_support C W0 W1 hW0 hW1
    (X k.val) (Y k.val) (hX k.val k.property) (hY k.val k.property)
  let R := F.attach.biUnion (fun k=>(hf k).toFinset)
  refine ⟨R,?_⟩
  intro k hk r hr
  by_contra hn
  apply hr
  exact Finset.mem_biUnion.mpr ⟨⟨k,hk⟩,by simp,by simpa only [Set.Finite.mem_toFinset,Function.mem_support] using hn⟩

theorem physical_selected_gaussian_reassembly {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (a : α→ℂ) (D : α→Id) (X Y : α→ℝ)
    (hX : ∀k∈F,0<X k) (hY : ∀k∈F,0<Y k) (Z : ℝ) (hZ : 0<Z)
    (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0<q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*markedPhysicalProbe η C (D k) W0 W1
      (X k) (Y k) (Z*∏i,q k i))=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*
        (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
          correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j))*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  obtain ⟨R,hR⟩ := physicalRows_common_finset C W0 W1 hW0 hW1 F X Y hX hY
  have hs (k : α) (hk : k∈F) (f : PhysicalRowIndex→ℂ) :
      (∑'r,physicalRowWeight C W0 W1 (X k) (Y k) r*f r)=
      ∑r∈R,physicalRowWeight C W0 W1 (X k) (Y k) r*f r :=
    tsum_eq_sum (fun r hr=>by rw [hR k hk r hr,zero_mul])
  let A (p : α×PhysicalRowIndex) := a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2
  have hh := gaussian_selected_tuple_reassembly W V hV hsep (F×ˢR) A C.excluded
    (fun p=>D p.1) (fun p=>physicalRowMonoid η C p.2)
    (fun p _=>physicalRowMonoid_norm η C p.2) Z hZ (fun p=>q p.1)
    (fun p hp=>hq p.1 (Finset.mem_product.mp hp).1)
  calc
    _ = ∑p∈F×ˢR,A p*(∏i,W i (q p.1 i))*correctedCompletedT C.excluded (D p.1)
      (physicalRowMonoid η C p.2) gaussianCompletedProfile (Z*∏i,q p.1 i) := by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro k hk
        rw [markedPhysicalProbe_eq_gaussian_rows η C (D k) W0 W1 hW0 hW1
          (X k) (Y k) _ (hX k hk) (hY k hk) (mul_pos hZ (Finset.prod_pos (fun i _=>hq k hk i))),hs k hk]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        dsimp [A]
        ring
    _ = _ := hh
    _ = _ := by
      apply tsum_congr
      intro j
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      congr 1
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hs k hk,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      dsimp [A]
      ring

theorem physical_selected_gaussian_family {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀J : ℕ,∀s : ℝ,0<s→∃B : ℝ,0<B ∧ ∀Z : ℝ,0<Z→
        Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)) ∧
        (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z))≤B*Z^s) ∧
      (∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
        HasCompactSupport W0→HasCompactSupport W1→
        ∀F : Finset α,∀a : α→ℂ,∀D : α→Id,∀X Y : α→ℝ,
        (∀k∈F,0<X k)→(∀k∈F,0<Y k)→∀Z : ℝ,0<Z→
        ∀q : α→ι→ℝ,(∀k∈F,∀i,0<q k i)→
        (∑k∈F,a k*(∏i,W i (q k i))*markedPhysicalProbe η C (D k) W0 W1
          (X k) (Y k) (Z*∏i,q k i))=
          ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*
            (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
              correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
                (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j))*
            (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
              gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
  obtain ⟨V,hV,hsep,_⟩ := gaussian_selected_slot_family W M hM hwindow
  refine ⟨V,hV,fun J s hs=>gaussianJointMoment_summed V hV J s hs,?_⟩
  intro η C W0 W1 hW0 hW1 F a D X Y hX hY Z hZ q hq
  exact physical_selected_gaussian_reassembly W V hV hsep η C W0 W1 hW0 hW1
    F a D X Y hX hY Z hZ q hq

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianCompensation -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalElementNorm_pos (a : O) (ha : a≠0) : 0<elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

lemma elementNorm_slotProduct {K : ℕ} (p : Fin K→O) (J : Finset (Fin K)) :
    elementNorm (slotProduct p J)=∏i∈J,elementNorm (p i) := by
  induction J using Finset.induction_on with
  | empty => simp [slotProduct,elementNorm_one]
  | @insert i J hi ih => simpa only [slotProduct,Finset.prod_insert hi,elementNorm_mul] using congrArg (fun x=>elementNorm (p i)*x) ih

lemma slotProduct_nonzero {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    slotProduct p J≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)

lemma slotProduct_norm_pos {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    0<elementNorm (slotProduct p J) := physicalElementNorm_pos _ (slotProduct_nonzero p hp J)

def compensationSubsetCoefficient {K : ℕ} (η : HeckeFamily.Character)
    (p : Fin K→O) (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (slotProduct p J)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (slotProduct p (Finset.univ\J)))

def compensationSubsetProbe {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (J : Finset (Fin K)) (X Y Z : ℝ) : ℂ :=
  compensationSubsetCoefficient η p J*
    markedPhysicalProbe η C (Ideal.span {slotProduct p (Finset.univ\J)}) W0 W1
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (Z*elementNorm (slotProduct p (Finset.univ\J)))

lemma compensatedTuple_eq_subsets {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (X Y Z : ℝ) :
    compensatedTuple η C W0 W1 p X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,compensationSubsetProbe η C W0 W1 p J X Y Z := rfl

lemma compensatedPhysicalProbe_eq_subsets {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slotPrimes : Fin K→Finset O)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (X Y Z : ℝ) :
    compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,
        ∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
          (∏i,W i (elementNorm (p i).val/P i))*
            compensationSubsetProbe η C W0 W1 (fun i=>(p i).val) J X Y Z := by
  unfold compensatedPhysicalProbe
  simp_rw [compensatedTuple_eq_subsets,Finset.mul_sum]
  exact Finset.sum_comm

theorem compensationSubsetProbe_eq_gaussian_rows {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensationSubsetProbe η C W0 W1 p J X Y Z=
      compensationSubsetCoefficient η p J*
        ∑'r : PhysicalRowIndex,
          physicalRowWeight C W0 W1 (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J)) r*
            correctedCompletedT C.excluded (Ideal.span {slotProduct p (Finset.univ\J)})
              (physicalRowMonoid η C r) gaussianCompletedProfile
                (Z*elementNorm (slotProduct p (Finset.univ\J))) := by
  unfold compensationSubsetProbe
  rw [markedPhysicalProbe_eq_gaussian_rows η C _ W0 W1 hW0 hW1 _ _ _
    (div_pos hX (slotProduct_norm_pos p hp J)) (div_pos hY (slotProduct_norm_pos p hp J))
    (mul_pos hZ (slotProduct_norm_pos p hp _))]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianPhysicalTail -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss FourierBridge
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianPhysicalFamilyIntegral {α ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (F : Finset α) (a : α→ℂ) (D : α→Id) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) : ℂ :=
  ∫t : ℝ,(∑k∈F,a k*
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
      correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T)*
    (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t

def gaussianPhysicalFamilyMass {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*(∏i,‖W i (q k i)‖)*∑'r : PhysicalRowIndex,‖physicalRowWeight C W0 W1 (X k) (Y k) r‖

lemma gaussianPhysicalFamily_mass_eq {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (R : Finset PhysicalRowIndex)
    (hR : ∀k∈F,∀r∉R,physicalRowWeight C W0 W1 (X k) (Y k) r=0) :
    gaussianCompletedFamilyMass (F×ˢR)
      (fun p=>a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2) W (fun p=>q p.1)=
      gaussianPhysicalFamilyMass C W0 W1 F a X Y W q := by
  unfold gaussianCompletedFamilyMass gaussianPhysicalFamilyMass
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [tsum_eq_sum (s:=R) (fun r hr=>by rw [hR k hk r hr,norm_zero]),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [norm_mul]
  ring

lemma gaussianPhysicalFamily_integral_eq {α ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (F : Finset α) (a : α→ℂ) (D : α→Id) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) (R : Finset PhysicalRowIndex)
    (hR : ∀k∈F,∀r∉R,physicalRowWeight C W0 W1 (X k) (Y k) r=0) :
    gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV T Z=
      gaussianCompletedFamilyIntegral (F×ˢR)
        (fun p=>a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2)
        C.excluded (fun p=>D p.1) (fun p=>physicalRowMonoid η C p.2) W (fun p=>q p.1) V hV T Z := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [tsum_eq_sum (s:=R) (fun r hr=>by rw [hR k hk r hr,zero_mul]),Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem gaussianPhysicalFamily_remote (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ) :
    ∃C0 : ℝ,0<C0 ∧ ∀{α ι : Type*} [Fintype ι],
      ∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
      HasCompactSupport W0→HasCompactSupport W1→
      ∀F : Finset α,∀a : α→ℂ,∀D : α→Id,∀X Y : α→ℝ,
      (∀k∈F,0<X k)→(∀k∈F,0<Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          C0*gaussianPhysicalFamilyMass C W0 W1 F a X Y W q*Z^2/A^N := by
  obtain ⟨C0,hC0,hb⟩ := gaussianCompletedFamily_remote V hV N
  refine ⟨C0,hC0,?_⟩
  intro α ι _ η C W0 W1 hW0 hW1 F a D X Y hX hY W q Z A hZ hA
  obtain ⟨R,hR⟩ := physicalRows_common_finset C W0 W1 hW0 hW1 F X Y hX hY
  have hh := hb (F×ˢR) (fun p=>a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2)
    C.excluded (fun p=>D p.1) (fun p=>physicalRowMonoid η C p.2)
    (fun p _=>physicalRowMonoid_norm η C p.2) W (fun p=>q p.1) Z A hZ hA
  rw [gaussianPhysicalFamily_mass_eq C W0 W1 F a X Y W q R hR] at hh
  simpa only [gaussianPhysicalFamily_integral_eq η C W0 W1 F a D X Y W q V hV _ Z R hR] using hh

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianSubset -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev SelectedSlot {K : ℕ} (J : Finset (Fin K)) := ↥(Finset.univ\J)

def compensationSubsetWeight {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (p : Fin K→O) (J : Finset (Fin K)) : ℂ :=
  compensationSubsetCoefficient η p J*(∏i∈J,W i (elementNorm (p i)/P i))

def selectedSlotFactor {K : ℕ} (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (p : Fin K→O) (J : Finset (Fin K)) (t : ℝ) : ℂ :=
  ∏i : SelectedSlot J,W i.val (elementNorm (p i.val)/P i.val)*
    logPhase (-t) (Real.log (elementNorm (p i.val)/P i.val))

def compensationRowTest {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (J : Finset (Fin K)) (X Y T t : ℝ) : ℂ :=
  ∑'r : PhysicalRowIndex,
    physicalRowWeight C W0 W1 (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J)) r*
      correctedCompletedT C.excluded (Ideal.span {slotProduct p (Finset.univ\J)})
        (physicalRowMonoid η C r) (CompletedHeight.normTwistedSource gaussianFixedWindow t) T

lemma gaussian_slot_window_split {K : ℕ} (W : Fin K→ℝ→ℂ) (q : Fin K→ℝ) (J : Finset (Fin K)) :
    (∏i,W i (q i))=(∏i∈J,W i (q i))*(∏i : SelectedSlot J,W i.val (q i.val)) := by
  rw [Finset.prod_coe_sort (Finset.univ\J) (fun i=>W i (q i))]
  have hh := Finset.prod_sdiff (Finset.subset_univ J) (f:=fun i=>W i (q i))
  simpa only [mul_comm] using hh.symm

lemma gaussian_compensation_scale {K : ℕ} (P : Fin K→ℝ) (hP : ∀i,0<P i)
    (p : Fin K→O) (J : Finset (Fin K)) (Z : ℝ) :
    (Z*∏i∈Finset.univ\J,P i)*(∏i : SelectedSlot J,elementNorm (p i.val)/P i.val)=
      Z*elementNorm (slotProduct p (Finset.univ\J)) := by
  rw [←Finset.prod_coe_sort (Finset.univ\J) P]
  rw [gaussian_selected_scale Z (fun i : SelectedSlot J=>P i.val)
    (fun i : SelectedSlot J=>elementNorm (p i.val)) (fun i=>hP i.val)]
  rw [Finset.prod_coe_sort (Finset.univ\J) (fun i=>elementNorm (p i)),elementNorm_slotProduct]

theorem compensation_subset_common {K : ℕ} {α : Type*}
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : SelectedSlot J→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i.val (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i.val (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (p : α→Fin K→O) (hp : ∀k∈F,∀i,p k i≠0)
    (P : Fin K→ℝ) (hP : ∀i,0<P i) (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∑k∈F,(∏i,W i (elementNorm (p k i)/P i))*compensationSubsetProbe η C W0 W1 (p k) J X Y Z)=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,compensationSubsetWeight η W P (p k) J*
        compensationRowTest η C W0 W1 (p k) J X Y ((2:ℝ)^j) t*
          selectedSlotFactor W P (p k) J t)*
            gaussianJointDensity V hV ((2:ℝ)^j/(Z*∏i∈Finset.univ\J,P i)) t := by
  have hbase : 0<Z*∏i∈Finset.univ\J,P i := mul_pos hZ (Finset.prod_pos (fun i _=>hP i))
  have hh := physical_selected_gaussian_reassembly
    (fun i : SelectedSlot J=>W i.val) V hV hsep η C W0 W1 hW0 hW1 F
    (fun k=>compensationSubsetWeight η W P (p k) J)
    (fun k=>Ideal.span {slotProduct (p k) (Finset.univ\J)})
    (fun k=>X/elementNorm (slotProduct (p k) J)) (fun k=>Y/elementNorm (slotProduct (p k) J))
    (fun k hk=>div_pos hX (slotProduct_norm_pos (p k) (hp k hk) J))
    (fun k hk=>div_pos hY (slotProduct_norm_pos (p k) (hp k hk) J))
    (Z*∏i∈Finset.univ\J,P i) hbase
    (fun k (i : SelectedSlot J)=>elementNorm (p k i.val)/P i.val)
    (fun k hk i=>div_pos (physicalElementNorm_pos _ (hp k hk i.val)) (hP i.val))
  calc
    _ = ∑k∈F,compensationSubsetWeight η W P (p k) J*
      (∏i : SelectedSlot J,W i.val (elementNorm (p k i.val)/P i.val))*
        markedPhysicalProbe η C (Ideal.span {slotProduct (p k) (Finset.univ\J)}) W0 W1
          (X/elementNorm (slotProduct (p k) J)) (Y/elementNorm (slotProduct (p k) J))
          ((Z*∏i∈Finset.univ\J,P i)*(∏i : SelectedSlot J,elementNorm (p k i.val)/P i.val)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [gaussian_compensation_scale P hP (p k) J Z,gaussian_slot_window_split W (fun i=>elementNorm (p k i)/P i) J]
      unfold compensationSubsetProbe compensationSubsetWeight
      ring
    _ = _ := hh

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianCommon -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

theorem compensatedPhysicalProbe_common_gaussian {K : ℕ}
    (W : Fin K→ℝ→ℂ) (M : Fin K→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : Finset (Fin K)→SchwartzMap ℝ ℂ,
    ∃hV : ∀A,HasCompactSupport (V A:ℝ→ℂ),
      (∀N : ℕ,∀s : ℝ,0<s→∃B : ℝ,0<B ∧
        ∀A : Finset (Fin K),∀Z : ℝ,0<Z→
          Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z)) ∧
          (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z))≤B*Z^s) ∧
      (∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
        HasCompactSupport W0→HasCompactSupport W1→
        ∀slotPrimes : Fin K→Finset O,(∀i a,a∈slotPrimes i→a≠0)→
        ∀P : Fin K→ℝ,(∀i,0<P i)→∀X Y Z : ℝ,0<X→0<Y→0<Z→
          compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
          ∑A∈(Finset.univ : Finset (Fin K)).powerset,
            ∑'j : ℕ,∫t : ℝ,
              (∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
                compensationSubsetWeight η W P (fun i=>(p i).val) A*
                  compensationRowTest η C W0 W1 (fun i=>(p i).val) A X Y ((2:ℝ)^j) t*
                    selectedSlotFactor W P (fun i=>(p i).val) A t)*
                      gaussianJointDensity (V A) (hV A) ((2:ℝ)^j/(Z*∏i∈Finset.univ\A,P i)) t) := by
  choose V hV hsep hbound using fun A : Finset (Fin K)=>
    gaussian_selected_slot_family (fun i : SelectedSlot A=>W i.val)
      (fun i : SelectedSlot A=>M i.val) (fun i=>hM i.val) (fun i=>hwindow i.val)
  refine ⟨V,hV,?_,?_⟩
  · intro N s hs
    choose B hB hb using fun A : Finset (Fin K)=>gaussianJointMoment_summed (V A) (hV A) N s hs
    let B0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,B A)+1
    have hB0 : 0<B0 := by
      have hh : 0≤∑A∈(Finset.univ : Finset (Fin K)).powerset,B A :=
        Finset.sum_nonneg (fun A _=>(hB A).le)
      dsimp only [B0]
      linarith
    refine ⟨B0,hB0,?_⟩
    intro A Z hZ
    obtain ⟨hsm,hbd⟩ := hb A Z hZ
    refine ⟨hsm,hbd.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le s)
    have hm : A∈(Finset.univ : Finset (Fin K)).powerset := Finset.mem_powerset.mpr (Finset.subset_univ A)
    have hh := Finset.single_le_sum (fun A _=>(hB A).le) hm
    dsimp only [B0]
    linarith
  · intro η C W0 W1 hW0 hW1 slotPrimes hp P hP X Y Z hX hY hZ
    rw [compensatedPhysicalProbe_eq_subsets]
    apply Finset.sum_congr rfl
    intro A hA
    exact compensation_subset_common A W (V A) (hV A) (hsep A) η C W0 W1 hW0 hW1 Finset.univ
      (fun p : ((i : Fin K)→{a : O // a∈slotPrimes i})=>fun i=>(p i).val)
      (fun p _ i=>hp i (p i).val (p i).property) P hP X Y Z hX hY hZ

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowRay -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open RayFourExpansion CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PhysicalRayElement := {s : O // Supported (Ideal.span {s})}

def physicalRay (s : O) : RayRing := Ideal.Quotient.mk (Ideal.span {(4:O)}) s

def physicalRayRepresentative (σ : RayRing) : PhysicalRayElement :=
  if h : ∃s : PhysicalRayElement,physicalRay s.val=σ then Classical.choose h
  else ⟨1,by
    simp [Supported,Ideal.span_singleton_one,←Ideal.one_eq_top]
    change (1:Id)≠0
    exact one_ne_zero⟩

lemma physicalRayRepresentative_spec (s : PhysicalRayElement) :
    physicalRay (physicalRayRepresentative (physicalRay s.val)).val=physicalRay s.val := by
  have hh : ∃r : PhysicalRayElement,physicalRay r.val=physicalRay s.val := ⟨s,rfl⟩
  simp only [physicalRayRepresentative,dite_eq_left hh]
  exact Classical.choose_spec hh

lemma rowCoefficient_congr_ray (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s r : PhysicalRayElement) (h : physicalRay s.val=physicalRay r.val) (m : O) :
    rowCoefficient η Xi s.val s.property m=rowCoefficient η Xi r.val r.property m := by
  apply MonoidHom.ext
  intro n
  rw [rowCoefficient_apply,rowCoefficient_apply]
  have hd : (4:O)∣s.val-r.val := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have he : sexticReciprocityPhase s.val n=sexticReciprocityPhase r.val n := by
    unfold sexticReciprocityPhase
    rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub s.val r.val hd]
  rw [he]

def physicalRayRowMonoid (η : HeckeFamily.Character) (C : CalibrationData)
    (σ : RayRing) (m : O) : O→*ℂ :=
  rowCoefficient η C.Xi (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m

def physicalIdealRay (s : {I : Id // Supported I}) : RayRing := physicalRay (primaryGenerator s.val)

lemma physicalRowMonoid_eq_ray (η : HeckeFamily.Character) (C : CalibrationData) (r : PhysicalRowIndex) :
    physicalRowMonoid η C r=physicalRayRowMonoid η C (physicalIdealRay r.1) r.2 := by
  let s : PhysicalRayElement :=
    ⟨primaryGenerator r.1.val,(supported_span_primaryGenerator_iff r.1.val).mpr r.1.property⟩
  exact rowCoefficient_congr_ray η C.Xi s (physicalRayRepresentative (physicalRay s.val))
    (physicalRayRepresentative_spec s).symm r.2

lemma physicalRayRowMonoid_norm (η : HeckeFamily.Character) (C : CalibrationData)
    (σ : RayRing) (m n : O) : ‖physicalRayRowMonoid η C σ m n‖≤1 :=
  rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ m n

def physicalRayPeriodicBase (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) : O→*ℂ :=
  lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) (physicalRayRepresentative σ).val
      (physicalRayRepresentative σ).property χ

theorem physicalRayPeriodicBase_uniform (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) :
    ∃L : Id,L≠0 ∧ ∀σ : RayRing,∀χ : RayCharacter,
      FactorsModulo L (physicalRayPeriodicBase η S hS σ χ) ∧
      ∀n : O,‖physicalRayPeriodicBase η S hS σ χ n‖≤1 := by
  refine ⟨lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS),
    lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _,?_⟩
  intro σ χ
  exact ⟨lowPeriodicBase_periodic η _ _ _ _ _ χ,lowPeriodicBase_norm η _ _ _ _ _ χ⟩

theorem physicalRayRow_eq_periodic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (σ : RayRing) (m : O) (D : Id) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (T : ℝ) (hT : 0<T) :
    correctedCompletedT S D (physicalRayRowMonoid η (calibrationForSet S hS) σ m) W T=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator 1 m)
          W T (fun A=>if D∣A then (1:ℂ) else 0) :=
  correctedPhysicalRow_eq_periodic_inverse η S hS hbad
    (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m D W hW T hT
      (calibrationLowData S hS)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowCutoff -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

def lowOuterCutoff (a b x : ℝ) : ℂ :=
  (Real.smoothTransition (2*x/a-1):ℂ)*(Real.smoothTransition (2-x/b):ℂ)

lemma lowOuterCutoff_small (a b : ℝ) (ha : 0<a) (x : ℝ) (hx : x≤a/2) :
    lowOuterCutoff a b x=0 := by
  have h : 2*x/a-1≤0 := by
    have hh : 2*x/a≤1 := (div_le_iff₀ ha).mpr (by linarith)
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.zero_of_nonpos h,Complex.ofReal_zero,zero_mul]

lemma lowOuterCutoff_large (a b : ℝ) (hb : 0<b) (x : ℝ) (hx : 2*b≤x) :
    lowOuterCutoff a b x=0 := by
  have h : 2-x/b≤0 := by
    have hh : 2≤x/b := (le_div_iff₀ hb).mpr hx
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.zero_of_nonpos h,Complex.ofReal_zero,mul_zero]

lemma lowOuterCutoff_one (a b : ℝ) (ha : 0<a) (hb : 0<b) (x : ℝ) (hlo : a≤x) (hhi : x≤b) :
    lowOuterCutoff a b x=1 := by
  have hl : 1≤2*x/a-1 := by
    have hh : 2≤2*x/a := (le_div_iff₀ ha).mpr (by linarith)
    linarith
  have hr : 1≤2-x/b := by
    have hh : x/b≤1 := (div_le_iff₀ hb).mpr (by simpa using hhi)
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.one_of_one_le hl,
    Real.smoothTransition.one_of_one_le hr,Complex.ofReal_one,mul_one]

lemma lowOuterCutoff_smooth (a b : ℝ) : ContDiff ℝ ∞ (lowOuterCutoff a b) := by
  unfold lowOuterCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).mul
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))

lemma lowOuterCutoff_support (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Function.support (lowOuterCutoff a b)⊆Set.Icc (a/2) (2*b) := by
  intro x hx
  constructor
  · by_contra hh
    exact hx (lowOuterCutoff_small a b ha x (le_of_lt (lt_of_not_ge hh)))
  · by_contra hh
    exact hx (lowOuterCutoff_large a b hb x (le_of_lt (lt_of_not_ge hh)))

lemma lowOuterCutoff_compact (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    HasCompactSupport (lowOuterCutoff a b) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (lowOuterCutoff_support a b ha hb)

lemma physical_ratio_factor (B q X Y m : ℝ) (hq : 0<q) (hY : 0<Y) :
    m/(B*X*Y)=(q/Y)*(m/(B*q*X)) := by
  field_simp

lemma physical_window_cutoff_one (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (B q X Y m : ℝ) (hq : 0<q) (hY : 0<Y)
    (h0 : W0 (m/(B*q*X))≠0) (h1 : W1 (q/Y)≠0) :
    lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (m/(B*X*Y))=1 := by
  have h0b := hW0 h0
  have h1b := hW1 h1
  apply lowOuterCutoff_one _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  · rw [physical_ratio_factor B q X Y m hq hY]
    have hh := mul_le_mul h0b.1 h1b.1 ha1.le (le_trans ha0.le h0b.1)
    simpa only [mul_comm] using hh
  · rw [physical_ratio_factor B q X Y m hq hY]
    have hh := mul_le_mul h0b.2 h1b.2 (le_trans ha1.le h1b.1) (le_trans ha0.le (h0b.1.trans h0b.2))
    have hd : (q/Y)*(m/(B*q*X))≤b0*b1 := by simpa only [mul_comm] using hh
    exact hd.trans (le_max_right _ _)

theorem physicalRowWeight_insert_cutoff (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y : ℝ) (hY : 0<Y) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (elementNorm r.2/(elementNorm C.generator*X*Y))*
        physicalRowWeight C W0 W1 X Y r := by
  by_cases hz : physicalRowWeight C W0 W1 X Y r=0
  · simp only [hz,mul_zero]
  have h0 : W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))≠0 :=
    fun h=>hz (physicalRowWeight_inner_zero C W0 W1 X Y r h)
  have h1 : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)≠0 :=
    fun h=>hz (physicalRowWeight_outer_zero C W0 W1 X Y r h)
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  rw [physical_window_cutoff_one W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (elementNorm C.generator) (Ideal.absNorm r.1.val) X Y (elementNorm r.2) hq hY h0 h1,one_mul]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowMellin -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical

lemma low_mellin_phase_norm (a v : ℝ) (ha : 0<a) :
    ‖(a:ℂ)^((v:ℂ)*Complex.I)‖=1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]
  simp

lemma low_mellin_ratio_integrable (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Integrable (fun v : ℝ=>(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)*
      mellin W ((v:ℂ)*Complex.I)) := by
  have hm : Integrable (fun v : ℝ=>mellin W ((v:ℂ)*Complex.I)) := by
    have hh := compactMellin_vertical_integrable W a0 b0 ha0 hW hWs 0
    change Integrable (fun v : ℝ=>mellin W ((0:ℂ)+v*Complex.I)) at hh
    simpa using hh
  have hc : Continuous (fun v : ℝ=>(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne')))
  have hp : ∀v : ℝ,‖(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)‖≤1 := by
    intro v
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ha,Complex.norm_cpow_eq_rpow_re_of_pos hb]
    simp
  simpa only [mul_comm] using hm.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hp)

lemma low_mellin_ratio (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    W (a/b)=(1/(2*Real.pi):ℂ)*∫v : ℝ,
      (a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I) := by
  rw [compactMellin_inversion W a0 b0 ha0 hW hWs 0 _ (div_pos ha hb)]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  rw [Complex.ofReal_zero,zero_add,Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg ha.le hb.le]
  simp only [div_eq_mul_inv,←Complex.cpow_neg,neg_neg]

lemma low_sqrt_ratio (B q X Y : ℝ) (hB : 0<B) (hq : 0<q) (hX : 0<X) (hY : 0<Y) :
    (Real.sqrt (B*q*X):ℂ)⁻¹=
      (Real.sqrt (B*X*Y):ℂ)⁻¹*((q/Y:ℝ):ℂ)^(-(1/2:ℂ)) := by
  have hQ : 0<B*X*Y := by positivity
  have hb : 0<q/Y := div_pos hq hY
  have he : B*q*X=(B*X*Y)*(q/Y) := by field_simp
  rw [he,Real.sqrt_mul hQ.le,Complex.ofReal_mul,Complex.cpow_neg,ProbeEuler.cpow_half_eq_sqrt _ hb.le]
  simp only [mul_inv_rev,mul_comm]

theorem physical_radial_low_mellin (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (B q X Y m : ℝ) (hB : 0<B) (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hm : 0< m) :
    (Real.sqrt (B*q*X):ℂ)⁻¹*W (m/(B*q*X))=
      (Real.sqrt (B*X*Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
          ((q/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I) := by
  have hQ : 0<B*X*Y := by positivity
  have ha : 0< m/(B*X*Y) := div_pos hm hQ
  have hb : 0<q/Y := div_pos hq hY
  have hbc : ((q/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have he : m/(B*q*X)=(m/(B*X*Y))/(q/Y) := by field_simp
  rw [he,low_mellin_ratio W a0 b0 ha0 hW hWs _ _ ha hb,low_sqrt_ratio B q X Y hB hq hX hY]
  simp_rw [Complex.cpow_add _ _ hbc]
  rw [show (fun v : ℝ=>((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
    (((q/Y:ℝ):ℂ)^(-(1/2:ℂ))*((q/Y:ℝ):ℂ)^((v:ℂ)*Complex.I))*mellin W ((v:ℂ)*Complex.I))=
    (fun v : ℝ=>((q/Y:ℝ):ℂ)^(-(1/2:ℂ))*
      (((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*((q/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I))) by funext v; ring]
  rw [integral_const_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowRowMellin -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowAdditiveCoefficient (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) : ℂ :=
  if ∀P∈C.excluded,¬P∣s.val then
    let a := primaryGenerator s.val
    let ha := supported_primaryGenerator_ne_zero s.val s.property
    let q : ℝ := Ideal.absNorm s.val
    (Y:ℂ)⁻¹*W1 (q/Y)*idealRowHom C.generator s.val/(C.tau*C.residueMonoid a)*
      ((q/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-m)
  else 0

def lowPhysicalScale (C : CalibrationData) (X Y : ℝ) : ℝ := elementNorm C.generator*X*Y

def lowRowMellinIntegrand (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) (v : ℝ) : ℂ :=
  mellin W0 ((v:ℂ)*Complex.I)*Ω (elementNorm r.2/lowPhysicalScale C X Y)*C.residueMonoid r.2*
    ((elementNorm r.2/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
      lowAdditiveCoefficient C W1 Y r.1 r.2 v

lemma calibration_elementNorm_pos (C : CalibrationData) : 0<elementNorm C.generator := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))

lemma lowPhysicalScale_pos (C : CalibrationData) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    0<lowPhysicalScale C X Y := mul_pos (mul_pos (calibration_elementNorm_pos C) hX) hY

lemma lowAdditiveCoefficient_outer_zero (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) (h : W1 ((Ideal.absNorm s.val:ℝ)/Y)=0) :
    lowAdditiveCoefficient C W1 Y s m v=0 := by
  unfold lowAdditiveCoefficient
  split_ifs <;> simp [h]

lemma lowRowMellinIntegrand_nonzero_form (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (hY : 0<Y) (r : PhysicalRowIndex) (v : ℝ)
    (hc : ∀P∈C.excluded,¬P∣r.1.val) :
    lowRowMellinIntegrand C W0 W1 Ω X Y r v=
      ((Y:ℂ)⁻¹*W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*idealRowHom C.generator r.1.val/
        (C.tau*C.residueMonoid (primaryGenerator r.1.val))*
          (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ))*
          (Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
          sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)*
          Ω (elementNorm r.2/lowPhysicalScale C X Y)*C.residueMonoid r.2)*
        (((elementNorm r.2/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
          (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*mellin W0 ((v:ℂ)*Complex.I)) := by
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  have hqc : (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (div_pos hq hY).ne'
  unfold lowRowMellinIntegrand lowAdditiveCoefficient
  rw [ite_eq_left hc]
  dsimp only
  rw [Complex.cpow_add _ _ hqc]
  ring

lemma lowRowMellinIntegrand_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hΩ : Ω 0=0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (r : PhysicalRowIndex) : Integrable (lowRowMellinIntegrand C W0 W1 Ω X Y r) := by
  by_cases hm : r.2=0
  · have he : lowRowMellinIntegrand C W0 W1 Ω X Y r=0 := by
      funext v
      simp [lowRowMellinIntegrand,hm,elementNorm,hΩ]
    rw [he]
    exact integrable_zero _ _ _
  by_cases hc : ∀P∈C.excluded,¬P∣r.1.val
  · have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
    have hmpos : 0<elementNorm r.2 := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
    change Integrable (fun v : ℝ=>lowRowMellinIntegrand C W0 W1 Ω X Y r v)
    simp_rw [lowRowMellinIntegrand_nonzero_form C W0 W1 Ω X Y hY r _ hc]
    exact (low_mellin_ratio_integrable W0 a0 b0 ha0 hW0 hWs _ _
      (div_pos hmpos (lowPhysicalScale_pos C X Y hX hY)) (div_pos hq hY)).const_mul _
  · have he : lowRowMellinIntegrand C W0 W1 Ω X Y r=0 := by
      funext v
      simp [lowRowMellinIntegrand,lowAdditiveCoefficient,hc]
    rw [he]
    exact integrable_zero _ _ _

theorem physicalRowWeight_low_mellin (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowRowMellinIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y r v := by
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  have hΩ : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  by_cases hm : r.2=0
  · have hw : W0 0=0 := by
      by_contra hh
      have hx := (hW0 hh).1
      linarith
    simp [physicalRowWeight,lowRowMellinIntegrand,hm,elementNorm,hw,hΩ,Ω]
  by_cases hc : ∀P∈C.excluded,¬P∣r.1.val
  · have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
    have hmpos : 0<elementNorm r.2 := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
    rw [physicalRowWeight_insert_cutoff C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hY r]
    unfold physicalRowWeight lowRowMellinIntegrand lowAdditiveCoefficient lowPhysicalScale
    dsimp only
    simp only [ite_eq_left hc]
    have hh := physical_radial_low_mellin W0 a0 b0 ha0 hW0 hWs
      (elementNorm C.generator) (Ideal.absNorm r.1.val) X Y (elementNorm r.2)
      (calibration_elementNorm_pos C) hq hX hY hmpos

    calc
      _ = (Ω (elementNorm r.2/(elementNorm C.generator*X*Y))*(Y:ℂ)⁻¹*
        W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*idealRowHom C.generator r.1.val*
        (C.tau*C.residueMonoid (primaryGenerator r.1.val))⁻¹*C.residueMonoid r.2*
        (Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
        sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2))*
        ((Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X):ℂ)⁻¹*
          W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))) := by dsimp only [Ω]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
      _ = _ := by
        rw [hh]
        repeat rw [←integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun v=>by dsimp only [Ω]; ring)
  · simp [physicalRowWeight,lowRowMellinIntegrand,lowAdditiveCoefficient,hc]

lemma lowAdditiveCoefficient_height (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ) (hY : 0<Y)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) :
    lowAdditiveCoefficient C W1 Y s m v=
      (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*lowAdditiveCoefficient C W1 Y s m 0 := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  have hqc : (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (div_pos hq hY).ne'
  unfold lowAdditiveCoefficient
  split_ifs
  · dsimp only
    rw [Complex.cpow_add _ _ hqc]
    simp only [Complex.ofReal_zero,zero_mul,add_zero]
    ring
  · simp

lemma lowAdditiveCoefficient_height_norm (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ) (hY : 0<Y)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) :
    ‖lowAdditiveCoefficient C W1 Y s m v‖=‖lowAdditiveCoefficient C W1 Y s m 0‖ := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  rw [lowAdditiveCoefficient_height C W1 Y hY s m v,norm_mul,
    low_mellin_phase_norm _ v (div_pos hq hY),one_mul]

def lowArithmeticCoefficient (C : CalibrationData) (s : {I : Id // Supported I}) : ℂ :=
  if ∀P∈C.excluded,¬P∣s.val then
    idealRowHom C.generator s.val/(C.tau*C.residueMonoid (primaryGenerator s.val))
  else 0

lemma calibration_residue_inverse_norm (C : CalibrationData) (a : O) : ‖(C.residueMonoid a)⁻¹‖≤1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero)
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  change ‖(C.residue (Ideal.Quotient.mk (Ideal.span {C.generator}) a))⁻¹‖≤1
  simpa only [MulChar.inv_apply_eq_inv'] using
    FiniteRayExpansion.norm_char_le_one C.residue⁻¹ (Ideal.Quotient.mk (Ideal.span {C.generator}) a)

lemma lowArithmeticCoefficient_norm (C : CalibrationData) (s : {I : Id // Supported I}) :
    ‖lowArithmeticCoefficient C s‖≤‖C.tau‖⁻¹ := by
  unfold lowArithmeticCoefficient
  split_ifs
  · simp only [div_eq_mul_inv,mul_inv_rev,norm_mul,norm_inv]
    have hi := calibration_residue_inverse_norm C (primaryGenerator s.val)
    rw [norm_inv] at hi
    have hh := (mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg _)) (idealRowHom_norm C.generator s.val)).trans hi
    simpa only [mul_assoc] using mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg C.tau)) hh
  · simp

lemma lowArithmeticCoefficient_source_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (s : {I : Id // Supported I}) : ‖lowArithmeticCoefficient (calibrationForSet S hS) s‖≤1 := by
  simpa only [calibrationForSet_tau_norm,inv_one] using lowArithmeticCoefficient_norm (calibrationForSet S hS) s

lemma lowAdditiveCoefficient_eq (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) :
    lowAdditiveCoefficient C W1 Y s m v=
      (Y:ℂ)⁻¹*W1 ((Ideal.absNorm s.val:ℝ)/Y)*lowArithmeticCoefficient C s*
        (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*
          (Real.sqrt (Ideal.absNorm s.val):ℂ)⁻¹*
            sexticGauss (primaryGenerator s.val) (supported_primaryGenerator_ne_zero s.val s.property) (-m) := by
  unfold lowAdditiveCoefficient lowArithmeticCoefficient
  split_ifs <;> simp only [mul_zero,zero_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowMellinFubini -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowRowMellinIntegrand_common_support (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    ∃R : Finset PhysicalRowIndex,∀v : ℝ,∀r∉R,
      lowRowMellinIntegrand C W0 W1 Ω X Y r v=0 := by
  have hs := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  have hm := elementWindow_finite_support Ω hΩ _ (lowPhysicalScale_pos C X Y hX hY)
  refine ⟨hs.toFinset×ˢhm.toFinset,?_⟩
  intro v r hr
  simp only [Finset.mem_product,Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support] at hr
  by_cases h : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)=0
  · unfold lowRowMellinIntegrand
    rw [lowAdditiveCoefficient_outer_zero C W1 Y r.1 r.2 v h,mul_zero]
  · have ho : Ω (elementNorm r.2/lowPhysicalScale C X Y)=0 := by
      by_contra ho
      exact hr ⟨h,ho⟩
    simp [lowRowMellinIntegrand,ho]

lemma lowRowMellinIntegrand_mul_summable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (v : ℝ) (B : PhysicalRowIndex→ℂ) :
    Summable (fun r=>lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r) := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  apply summable_of_ne_finset_zero (s:=R)
  intro r hr
  rw [hR v r hr,zero_mul]

lemma lowRowMellinIntegrand_sum_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    Integrable (fun v : ℝ=>∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r) := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  have he (v : ℝ) : (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∑r∈R,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
    apply tsum_eq_sum
    intro r hr
    rw [hR v r hr,zero_mul]
  simp_rw [he]
  exact integrable_finsetSum R (fun r _=>(lowRowMellinIntegrand_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hΩ0 X Y hX hY r).mul_const _)

lemma lowRowMellinIntegrand_tsum_integral (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    (∑'r : PhysicalRowIndex,∫v : ℝ,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∫v : ℝ,∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  have he (v : ℝ) : (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∑r∈R,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
    apply tsum_eq_sum
    intro r hr
    rw [hR v r hr,zero_mul]
  rw [tsum_eq_sum (s:=R) (fun r hr=>by simp only [hR _ r hr,zero_mul,integral_zero])]
  simp_rw [he]
  exact (integral_finsetSum R (fun r _=>(lowRowMellinIntegrand_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hΩ0 X Y hX hY r).mul_const _)).symm

theorem physicalRowWeight_tsum_low_mellin (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*B r)=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,∑'r : PhysicalRowIndex,
          lowRowMellinIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y r v*B r := by
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  have hΩ : HasCompactSupport Ω := lowOuterCutoff_compact _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hΩ0 : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  simp_rw [physicalRowWeight_low_mellin C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY]
  simp_rw [mul_assoc,←integral_mul_const]
  repeat rw [tsum_mul_left]
  congr 2
  exact lowRowMellinIntegrand_tsum_integral C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1c hΩ hΩ0 X Y hX hY B

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowRayAmplitude -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowRayAmplitude (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (m : O) (v : ℝ) : ℂ :=
  ∑'s : {I : Id // Supported I},if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0

lemma lowAdditiveCoefficient_common_support (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀m : O,∀v : ℝ,∀s∉F,
      lowAdditiveCoefficient C W1 Y s m v=0 := by
  have ho := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  refine ⟨ho.toFinset,?_⟩
  intro m v s hs
  apply lowAdditiveCoefficient_outer_zero
  simpa only [Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support,not_not] using hs

lemma lowAdditiveCoefficient_mul_summable (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (m : O) (v : ℝ)
    (F : {I : Id // Supported I}→ℂ) :
    Summable (fun s=>lowAdditiveCoefficient C W1 Y s m v*F s) := by
  obtain ⟨R,hR⟩ := lowAdditiveCoefficient_common_support C W1 hW1 Y hY
  apply summable_of_ne_finset_zero (s:=R)
  intro s hs
  rw [hR m v s hs,zero_mul]

lemma lowRayAmplitude_eq_finite (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀σ : RayRing,∀m : O,∀v : ℝ,
      lowRayAmplitude C W1 Y σ m v=
        ∑s∈F,if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0 := by
  obtain ⟨F,hF⟩ := lowAdditiveCoefficient_common_support C W1 hW1 Y hY
  refine ⟨F,?_⟩
  intro σ m v
  apply tsum_eq_sum
  intro s hs
  simp only [hF m v s hs,ite_self]

lemma lowRayAmplitude_group (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (m : O) (v : ℝ)
    (B : RayRing→ℂ) :
    (∑'s : {I : Id // Supported I},lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s))=
      ∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ := by
  obtain ⟨F,hF⟩ := lowAdditiveCoefficient_common_support C W1 hW1 Y hY
  have hleft : (∑'s : {I : Id // Supported I},lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s))=
      ∑s∈F,lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s) := by
    apply tsum_eq_sum
    intro s hs
    rw [hF m v s hs,zero_mul]
  have hr (σ : RayRing) : lowRayAmplitude C W1 Y σ m v=
      ∑s∈F,if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0 := by
    apply tsum_eq_sum
    intro s hs
    simp only [hF m v s hs,ite_self]
  rw [hleft]
  simp_rw [hr,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [ite_mul,zero_mul]
  simp

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowSeparated -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowSeparatedIntegrand (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (B : RayRing→O→ℂ) (v : ℝ) : ℂ :=
  mellin W0 ((v:ℂ)*Complex.I)*
    ∑'m : O,Ω (elementNorm m/lowPhysicalScale C X Y)*C.residueMonoid m*
      ((elementNorm m/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
        ∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ m

lemma lowSeparatedIntegrand_eq (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) (v : ℝ) :
    (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B (physicalIdealRay r.1) r.2)=
      lowSeparatedIntegrand C W0 W1 Ω X Y B v := by
  have hs := lowRowMellinIntegrand_mul_summable C W0 W1 Ω hW1 hΩ X Y hX hY v
    (fun r=>B (physicalIdealRay r.1) r.2)
  rw [hs.tsum_prod,←hs.tsum_comm]
  unfold lowSeparatedIntegrand
  rw [←tsum_mul_left]
  apply tsum_congr
  intro m
  rw [←lowRayAmplitude_group C W1 hW1 Y hY m v (fun σ=>B σ m)]
  repeat rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  unfold lowRowMellinIntegrand
  ring

lemma lowSeparatedIntegrand_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    Integrable (lowSeparatedIntegrand C W0 W1 Ω X Y B) := by
  have hh := lowRowMellinIntegrand_sum_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1 hΩ hΩ0 X Y hX hY
    (fun r=>B (physicalIdealRay r.1) r.2)
  simpa only [lowSeparatedIntegrand_eq C W0 W1 Ω hW1 hΩ X Y hX hY B] using hh

theorem physicalRowWeight_low_separated (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*B (physicalIdealRay r.1) r.2)=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y B v := by
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  have hΩ := lowOuterCutoff_compact (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  rw [physicalRowWeight_tsum_low_mellin C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY]
  simp_rw [lowSeparatedIntegrand_eq C W0 W1 _ hW1c hΩ X Y hX hY B]

theorem markedPhysicalProbe_low_separated (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y
          (fun σ m=>correctedCompletedT C.excluded D (physicalRayRowMonoid η C σ m) gaussianCompletedProfile Z) v := by
  have hW0c : HasCompactSupport W0 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  rw [markedPhysicalProbe_eq_gaussian_rows η C D W0 W1 hW0c hW1c X Y Z hX hY hZ]
  simp_rw [physicalRowMonoid_eq_ray]
  exact physicalRowWeight_low_separated C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY
    (fun σ m=>correctedCompletedT C.excluded D (physicalRayRowMonoid η C σ m) gaussianCompletedProfile Z)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowCompensation -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted CanonicalRowCompletion RayFourExpansion ProbeRow CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowMarkedInverseRow (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (D : Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑χ : RayCharacter,correctionCoeff χ*
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator 1 m)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
      (fun A=>if D∣A then (1:ℂ) else 0)

lemma lowMarkedInverseRow_eq (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (D : Id) (T t : ℝ) (hT : 0<T)
    (σ : RayRing) (m : O) :
    correctedCompletedT S D (physicalRayRowMonoid η (calibrationForSet S hS) σ m)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T=
        lowMarkedInverseRow η S hS D T t σ m :=
  physicalRayRow_eq_periodic_inverse η S hS hbad σ m D _ (gaussianFixedWindow_twist_compact t) T hT

theorem compensationRowTest_low_separated {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    compensationRowTest η (calibrationForSet S hS) W0 W1 p J X Y T t=
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
          (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t) v := by
  unfold compensationRowTest
  simp_rw [physicalRowMonoid_eq_ray]
  have hC : (calibrationForSet S hS).excluded=S := calibrationForSet_excluded S hS
  rw [hC]
  simp_rw [lowMarkedInverseRow_eq η S hS hbad _ T t hT]
  exact physicalRowWeight_low_separated (calibrationForSet S hS) W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hWs _ _ (div_pos hX (slotProduct_norm_pos p hp J))
      (div_pos hY (slotProduct_norm_pos p hp J))
      (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t)

lemma compensationRowTest_low_integrable {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) :
    Integrable (lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
      (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t)) := by
  exact lowSeparatedIntegrand_integrable (calibrationForSet S hS) W0 W1 _ a0 b0 ha0 hW0 hWs
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    (lowOuterCutoff_compact _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
    (lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)) _ _
    (div_pos hX (slotProduct_norm_pos p hp J)) (div_pos hY (slotProduct_norm_pos p hp J)) _

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowSelectedSum -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowSeparatedIntegrand_finite_sum {α : Type*} (F : Finset α) (c : α→ℂ)
    (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ) (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : α→RayRing→O→ℂ) (v : ℝ) :
    (∑k∈F,c k*lowSeparatedIntegrand C W0 W1 Ω X Y (B k) v)=
      lowSeparatedIntegrand C W0 W1 Ω X Y (fun σ m=>∑k∈F,c k*B k σ m) v := by
  simp_rw [←lowSeparatedIntegrand_eq C W0 W1 Ω hW1 hΩ X Y hX hY]
  simp_rw [←tsum_mul_left]
  rw [←Summable.tsum_finsetSum (fun k _=>
    (lowRowMellinIntegrand_mul_summable C W0 W1 Ω hW1 hΩ X Y hX hY v
      (fun r=>B k (physicalIdealRay r.1) r.2)).mul_left (c k))]
  apply tsum_congr
  intro r
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma lowSeparatedIntegral_finite_sum {α : Type*} (F : Finset α) (c : α→ℂ)
    (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : α→RayRing→O→ℂ) :
    (∑k∈F,c k*∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω X Y (B k) v)=
      ∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω X Y (fun σ m=>∑k∈F,c k*B k σ m) v := by
  simp_rw [←integral_const_mul]
  rw [←integral_finsetSum F (fun k _=>(lowSeparatedIntegrand_integrable C W0 W1 Ω
    a0 b0 ha0 hW0 hWs hW1 hΩ hΩ0 X Y hX hY (B k)).const_mul (c k))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v=>lowSeparatedIntegrand_finite_sum F c C W0 W1 Ω hW1 hΩ X Y hX hY B v)

def lowSelectedInverseRow {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑k∈F,c k*lowMarkedInverseRow η S hS (D k) T t σ m

lemma lowSelectedInverseRow_correction {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (m : O) :
    lowSelectedInverseRow F c η S hS D T t σ m=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        ∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
          (fun A=>if D k∣A then (1:ℂ) else 0) := by
  unfold lowSelectedInverseRow lowMarkedInverseRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro k hk
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowSlotSplit -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

abbrev LowUnselectedTuple {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :=
  ∀i : J,↥(slots i.val)
abbrev LowSelectedTuple {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :=
  ∀i : SelectedSlot J,↥(slots i.val)

def lowSlotTupleEquiv {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :
    (∀i,↥(slots i)) ≃ LowUnselectedTuple slots J×LowSelectedTuple slots J where
  toFun p := (fun i=>p i.val,fun i=>p i.val)
  invFun p i := if hi : i∈J then p.1 ⟨i,hi⟩ else p.2 ⟨i,by simp [hi]⟩
  left_inv p := by
    funext i
    dsimp only
    split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      simp only [dite_eq_left i.property]
    · funext i
      have hi : i.val∉J := (Finset.mem_sdiff.mp i.property).2
      simp only [dite_eq_right hi]

def lowSlotJoin {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) : Fin K→O :=
  fun i=>((lowSlotTupleEquiv slots J).symm (a,b) i).val

lemma lowSlotJoin_nonzero {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : Fin K) :
    lowSlotJoin slots J a b i≠0 := hslots i _ ((lowSlotTupleEquiv slots J).symm (a,b) i).property

lemma lowSlotJoin_unselected {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : J) :
    lowSlotJoin slots J a b i.val=(a i).val := by
  simp only [lowSlotJoin,lowSlotTupleEquiv,Equiv.coe_fn_symm_mk,dite_eq_left i.property]

lemma lowSlotJoin_selected {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : SelectedSlot J) :
    lowSlotJoin slots J a b i.val=(b i).val := by
  have hi : i.val∉J := (Finset.mem_sdiff.mp i.property).2
  simp only [lowSlotJoin,lowSlotTupleEquiv,Equiv.coe_fn_symm_mk,dite_eq_right hi]

lemma lowSlotJoin_unselectedProduct {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    slotProduct (lowSlotJoin slots J a b) J=∏i : J,(a i).val := by
  unfold slotProduct
  rw [←Finset.prod_coe_sort J]
  simp only [lowSlotJoin_unselected]

lemma lowSlotJoin_selectedProduct {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    slotProduct (lowSlotJoin slots J a b) (Finset.univ\J)=∏i : SelectedSlot J,(b i).val := by
  unfold slotProduct
  rw [←Finset.prod_coe_sort (Finset.univ\J)]
  simp only [lowSlotJoin_selected]

lemma lowSlotJoin_selectedFactor {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ) :
    selectedSlotFactor W P (lowSlotJoin slots J a b) J t=
      ∏i : SelectedSlot J,W i.val (elementNorm (b i).val/P i.val)*
        FourierBridge.logPhase (-t) (Real.log (elementNorm (b i).val/P i.val)) := by
  unfold selectedSlotFactor
  simp only [lowSlotJoin_selected]

theorem sum_lowSlotJoin {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(slots i)),F (fun i=>(p i).val))=
      ∑a : LowUnselectedTuple slots J,∑b : LowSelectedTuple slots J,F (lowSlotJoin slots J a b) := by
  calc
    _ = ∑p : LowUnselectedTuple slots J×LowSelectedTuple slots J,F (lowSlotJoin slots J p.1 p.2) :=
      (Equiv.sum_comp (lowSlotTupleEquiv slots J).symm (fun p=>F (fun i=>(p i).val))).symm
    _ = _ := Fintype.sum_prod_type _

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowSlotPolynomial -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowUnselectedWeight {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (a : LowUnselectedTuple slots J) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (∏i : J,(a i).val)^(-(3/2:ℝ)):ℝ):ℂ)*
    ∏i : J,W i.val (elementNorm (a i).val/P i.val)

def lowSelectedWeight {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) : ℂ :=
  star (HeckeFamily.elementCoeff η (∏i : SelectedSlot J,(b i).val))*
    ∏i : SelectedSlot J,W i.val (elementNorm (b i).val/P i.val)*
      FourierBridge.logPhase (-t) (Real.log (elementNorm (b i).val/P i.val))

def lowSelectedIdeal {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J) : Id := Ideal.span {∏i : SelectedSlot J,(b i).val}

lemma lowSlotJoin_weight {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    compensationSubsetWeight η W P (lowSlotJoin slots J a b) J*
      selectedSlotFactor W P (lowSlotJoin slots J a b) J t=
        lowUnselectedWeight slots J W P a*lowSelectedWeight η slots J W P t b := by
  unfold compensationSubsetWeight compensationSubsetCoefficient
  rw [lowSlotJoin_unselectedProduct,lowSlotJoin_selectedProduct,lowSlotJoin_selectedFactor]
  rw [←Finset.prod_coe_sort J (fun i=>W i (elementNorm (lowSlotJoin slots J a b i)/P i))]
  simp only [lowSlotJoin_unselected]
  unfold lowUnselectedWeight lowSelectedWeight
  ring

lemma lowUnselectedProduct_norm_pos {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    0<elementNorm (∏i : J,(a i).val) := by
  apply physicalElementNorm_pos
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>hslots i.val _ (a i).property)

lemma compensationRowTest_join_low {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J)
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    compensationRowTest η (calibrationForSet S hS) W0 W1 (lowSlotJoin slots J a b) J X Y T t=
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v := by
  simpa only [lowSlotJoin_unselectedProduct,lowSlotJoin_selectedProduct,lowSelectedIdeal] using
    compensationRowTest_low_separated η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs
      (lowSlotJoin slots J a b) (lowSlotJoin_nonzero slots hslots J a b) J X Y T t hX hY hT

theorem compensation_tuple_low_polynomial {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    (∑p : (∀i,↥(slots i)),compensationSubsetWeight η W P (fun i=>(p i).val) J*
      compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J X Y T t*
        selectedSlotFactor W P (fun i=>(p i).val) J t)=
      ∑a : LowUnselectedTuple slots J,lowUnselectedWeight slots J W P a*
        ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ))*
          ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
            (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
            (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
            (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W P t)
              η S hS (lowSelectedIdeal slots J) T t) v := by
  rw [sum_lowSlotJoin slots J (fun p=>compensationSubsetWeight η W P p J*
    compensationRowTest η (calibrationForSet S hS) W0 W1 p J X Y T t*selectedSlotFactor W P p J t)]
  apply Finset.sum_congr rfl
  intro a ha
  let L := elementNorm (∏i : J,(a i).val)
  have hL : 0<L := lowUnselectedProduct_norm_pos slots hslots J a
  let C := calibrationForSet S hS
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  let N : ℂ := (Real.sqrt (lowPhysicalScale C (X/L) (Y/L)):ℂ)⁻¹*(1/(2*Real.pi):ℂ)
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  have hΩc : HasCompactSupport Ω := lowOuterCutoff_compact _ _ (mul_pos ha0 ha1)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hΩ0 : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  calc
    _ = lowUnselectedWeight slots J W P a*N*
        ∑b : LowSelectedTuple slots J,lowSelectedWeight η slots J W P t b*
          ∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω (X/L) (Y/L)
            (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [compensationRowTest_join_low η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs
        slots hslots J a b X Y T t hX hY hT]
      have hw := lowSlotJoin_weight η slots J W P t a b
      dsimp only [C,Ω,L,N]
      linear_combination (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*
        (1/(2*Real.pi):ℂ)*(∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v)*hw
    _ = _ := by
      rw [lowSeparatedIntegral_finite_sum Finset.univ (lowSelectedWeight η slots J W P t)
        C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1c hΩc hΩ0 (X/L) (Y/L)
        (div_pos hX hL) (div_pos hY hL)]
      rfl

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowSlotWeights -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow FourierBridge
local notation "O" => ActualEisensteinCubic.O

def lowSingleSlotWeight (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) : ℂ :=
  star (HeckeFamily.elementCoeff η a)*W (elementNorm a/P)*logPhase (-t) (Real.log (elementNorm a/P))

lemma lowSelectedWeight_eq_product {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    lowSelectedWeight η slots J W P t b=
      ∏i : SelectedSlot J,lowSingleSlotWeight η (W i.val) (P i.val) t (b i).val := by
  have he : HeckeFamily.elementCoeff η (∏i : SelectedSlot J,(b i).val)=
      ∏i : SelectedSlot J,HeckeFamily.elementCoeff η (b i).val := map_prod (targetMonoid η) _ _
  unfold lowSelectedWeight lowSingleSlotWeight
  rw [he,star_prod]
  simp only [Finset.prod_mul_distrib,mul_assoc]

lemma lowSingleSlotWeight_norm (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) :
    ‖lowSingleSlotWeight η W P t a‖≤‖W (elementNorm a/P)‖ := by
  rw [lowSingleSlotWeight,norm_mul,norm_mul,norm_star,logPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)

lemma lowSingleSlotWeight_height_norm (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) :
    ‖lowSingleSlotWeight η W P t a‖=‖lowSingleSlotWeight η W P 0 a‖ := by
  simp only [lowSingleSlotWeight,norm_mul,logPhase_norm,mul_one]

lemma lowSelectedWeight_norm {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖≤∏i : SelectedSlot J,‖W i.val (elementNorm (b i).val/P i.val)‖ := by
  rw [lowSelectedWeight_eq_product,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>lowSingleSlotWeight_norm η (W i.val) (P i.val) t (b i).val)

lemma lowSelectedWeight_height_norm {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖=‖lowSelectedWeight η slots J W P 0 b‖ := by
  rw [lowSelectedWeight_eq_product,lowSelectedWeight_eq_product,norm_prod,norm_prod]
  exact Finset.prod_congr rfl (fun i _=>lowSingleSlotWeight_height_norm η (W i.val) (P i.val) t (b i).val)

lemma lowSelectedWeight_norm_le_one {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (hW : ∀i x,‖W i x‖≤1) (t : ℝ) (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖≤1 :=
  (lowSelectedWeight_norm η slots J W P t b).trans
    (Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>hW i.val _))

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SpectralPoisson -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def transformedSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (K : ℝ) (t : ℂ) (I J : Ideal O) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
        ∑' H : O, actualCongruenceCoefficient C (completedIndex I J) s hA H *
          paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s))
  else 0

theorem physical_spectral_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K : ℝ) (hK : 0<K) (t : ℂ) (ht : 1<t.re) :
    (∑' m : O, C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) *
      W (elementNorm m/K) * spectralRow S D (rowCoefficient η C.Xi s hs m) t) =
    ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C S D s hs W K t p.1 p.2 := by
  rw [physical_spectral_reopen η C S D s hs W hWc K hK t ht]
  apply tsum_congr
  intro p
  unfold transformedSpectralTerm
  by_cases hA : completedIndex p.1 p.2≠0
  · rw [dite_eq_left hA, physical_row_poisson C (completedIndex p.1 p.2) s hA
      (supportedElement_ne_zero s hs) W hWc hWs K hK]
    ring
  · rw [dite_eq_right hA, spectralSummand_zero_completedIndex S D p.1 p.2 _ t (not_ne_iff.mp hA), zero_mul]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.MellinPoisson -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

lemma finiteSupport_verticalIntegral {α : Type*} (c : α → ℂ)
    (hc : (Function.support c).Finite) (F : α → ℂ → ℂ) (σ : ℝ)
    (hF : ∀ a, Integrable (fun y : ℝ => F a ((σ:ℂ)+y*Complex.I))) :
    verticalIntegral σ (fun t => ∑' a, c a * F a t) =
      ∑' a, c a * verticalIntegral σ (F a) := by
  have hz (a : α) (ha : a∉hc.toFinset) : c a=0 := by
    simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using ha
  have he (t : ℂ) : (∑' a, c a*F a t) = ∑ a∈hc.toFinset, c a*F a t :=
    tsum_eq_sum (fun a ha => by rw [hz a ha, zero_mul])
  rw [tsum_eq_sum (s := hc.toFinset) (fun a ha => by rw [hz a ha, zero_mul])]
  unfold verticalIntegral
  simp_rw [he]
  rw [integral_finsetSum _ (fun a ha => (hF a).const_mul (c a)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_const_mul]
  ring

theorem inner_mellin_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K Z : ℝ) (hK : 0<K) (hZ : 0<Z) :
    (∑' m : O, C.residueMonoid m * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) *
      verticalIntegral 4 (fun t => (Z:ℂ)^t * Complex.exp (t^2) *
        spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) t)) =
    verticalIntegral 4 (fun t => (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      ((Z:ℂ)^t * Complex.exp (t^2)) *
        ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C C.excluded D s hs W K t p.1 p.2) := by
  let c (m : O) := C.residueMonoid m * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
    sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K)
  have hc : (Function.support c).Finite := by
    apply (elementWindow_finite_support W hWc K hK).subset
    intro m hm hz
    exact hm (by simp only [c, hz, mul_zero])
  rw [← finiteSupport_verticalIntegral c hc
    (fun m t => (Z:ℂ)^t * Complex.exp (t^2) *
      spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) t) 4
    (fun m => physicalRow_integrable η C D s hs m Z hZ)]
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  norm_num only [Complex.ofReal_ofNat]
  have ht : 1 < ((4:ℂ)+(y:ℂ)*Complex.I).re := by simp
  rw [← physical_spectral_poisson η C C.excluded D s hs W hWc hWs K hK _ ht,
    ← tsum_mul_left]
  apply tsum_congr
  intro m
  dsimp only [c]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.Transformed -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

def poissonPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  (Y:ℂ)⁻¹ * ∑' s : {I : Ideal O // Supported I},
    if ∀ p∈C.excluded, ¬p∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let q_s : ℝ := Ideal.absNorm s.val
      W₁ (q_s/Y) * CanonicalRowCompletion.idealRowHom C.generator s.val /
        (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q_s*X):ℂ)) *
      verticalIntegral 4 (fun t => (Real.sqrt q_s:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2)) *
        ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C C.excluded D a has W₀
          (elementNorm C.generator*q_s*X) t p.1 p.2)
    else 0

theorem markedPhysicalProbe_eq_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (hWc : HasCompactSupport W₀)
    (hWs : ContDiff ℝ ∞ W₀) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) :
    markedPhysicalProbe η C D W₀ W₁ X Y Z = poissonPhysicalProbe η C D W₀ W₁ X Y Z := by
  unfold markedPhysicalProbe poissonPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with h
  · dsimp only
    congr 1
    have ha := supported_primaryGenerator_ne_zero s.val s.property
    have has := (supported_span_primaryGenerator_iff s.val).mpr s.property
    have hn : elementNorm (primaryGenerator s.val) = (Ideal.absNorm s.val:ℝ) := by
      unfold elementNorm
      rw [(primaryGenerator_spec s.val ha).1]
    have hb : 0<elementNorm C.generator := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
    have hs : 0<(Ideal.absNorm s.val:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
    have hK : 0<elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X := mul_pos (mul_pos hb hs) hX
    simpa only [hn] using inner_mellin_poisson η C D (primaryGenerator s.val) has
      W₀ hWc hWs (elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X) Z hK hZ
  · rfl

theorem physicalProbe_eq_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (hWc : HasCompactSupport W₀) (hWs : ContDiff ℝ ∞ W₀)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) :
    physicalProbe η C W₀ W₁ X Y Z = poissonPhysicalProbe η C 1 W₀ W₁ X Y Z :=
  markedPhysicalProbe_eq_poisson η C 1 W₀ W₁ hWc hWs X Y Z hX hZ

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.ZeroIndex -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]

def zeroIndexTerm (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) (k m : ℕ) : ℂ :=
  (if k=0 then 1 else (χ^k) (Ideal.Quotient.mk _ (p^(6*m)))) * W^k * V^m

omit [(Ideal.span {p}).IsMaximal] in
lemma zeroIndex_inner_zero (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (hV : ‖V‖<1) :
    HasSum (fun m => zeroIndexTerm p χ W V 0 m) (1/(1-V)) := by
  simpa [zeroIndexTerm, one_div] using hasSum_geometric_of_norm_lt_one hV

include hp in
lemma zeroIndex_inner_pos (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (k : ℕ) (hk : k≠0) :
    HasSum (fun m => zeroIndexTerm p χ W V k m) (W^k) := by
  apply (hasSum_ite_eq 0 (W^k)).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hm
  dsimp only
  unfold zeroIndexTerm
  rw [ite_eq_right hk, zero_index_scalar p hp χ k (6*m) hk]
  by_cases h : m=0
  · subst m; simp
  · have h6 : 6*m≠0 := by omega
    simp [h, h6]

def zeroIndexSeries (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) : ℂ :=
  ∑' k, ∑' m, zeroIndexTerm p χ W V k m

include hp in
lemma zeroIndexSeries_eq (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (hW : ‖W‖<1) (hV : ‖V‖<1) :
    zeroIndexSeries p χ W V = 1/(1-V)+W/(1-W) := by
  have htail : HasSum (fun k => ∑' m, zeroIndexTerm p χ W V (k+1) m) (W/(1-W)) := by
    have he : (fun k => ∑' m, zeroIndexTerm p χ W V (k+1) m) =
        (fun k => W * W^k) := by
      funext k
      rw [(zeroIndex_inner_pos p hp χ W V (k+1) (by omega)).tsum_eq, pow_succ]
      ring
    rw [he]
    simpa [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hW).mul_left W
  have hall := HasSum.sum_range_add (f := fun k => ∑' m, zeroIndexTerm p χ W V k m) (k := 1) htail
  simpa only [zeroIndexSeries, Finset.sum_range_one,
    (zeroIndex_inner_zero p χ W V hV).tsum_eq] using hall.tsum_eq

end SevenEighths.ProbeEuler
end

end OAI

end

