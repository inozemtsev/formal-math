module

public import Green64.Library.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailKernel
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.IdealEuler.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part008

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Inversion / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailGeometry -/

section

namespace OAI

noncomputable section

open scoped Classical SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open InverseInitialProfile

theorem live_column_norm_bound (W : ℝ→ℂ) (b C v n X : ℝ)
    (hs : Function.support W⊆Set.Iic b) (hX : 0<X)
    (hw : W (C*v*n/X)≠0) : C*v*n≤b*X := by
  exact (div_le_iff₀ hX).mp (hs hw)

theorem actual_radial_center_lower
    (Z D m B θ H η C d v n₁ n₂ L hnorm : ℝ)
    (hZ : 1≤Z) (hd : 0<d) (hv : 0<v) (hn₁ : 0<n₁) (hn₂ : 0<n₂)
    (hL : 0<L) (hC : Z^B≤C) (hdiv : d≤Z^(θ+η))
    (hcol : L≤Z^(D+η)) (hfreq : Z^H≤hnorm)
    (h₁ : C*v*n₁≤L) (h₂ : C*v*n₂≤L) :
    Z^(radialCenter m H θ D B-3*η) ≤
      (Z^m/(d*v^2*n₁*n₂))*hnorm := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hc : 0<C := (Real.rpow_pos_of_pos hz B).trans_le hC
  have hh : 0≤hnorm := (Real.rpow_pos_of_pos hz H).le.trans hfreq
  have hscale := correlated_scale_lower (Z^m) C d v n₁ n₂ L
    (by positivity) hc hd hv hn₁ hn₂ hL h₁ h₂
  calc
    _ = Z^m*(Z^B)^2*Z^H/(Z^(θ+η)*(Z^(D+η))^2) := by
      simp only [pow_two]
      rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,
        ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_sub hz]
      congr 1
      unfold radialCenter
      ring
    _ ≤ Z^m*C^2*hnorm/(d*L^2) := by
      gcongr
    _ = (Z^m*C^2/(d*L^2))*hnorm := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale hh

theorem high_radial_block_tail_gate
    (Z D m B θ H η τ C d v n₁ n₂ L hnorm : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂) (hL : 0<L)
    (hC : Z^B≤C) (hdiv : d≤Z^(θ+η))
    (hcol : L≤Z^(D+η)) (hfreq : Z^H≤hnorm)
    (h₁ : C*v*n₁≤L) (h₂ : C*v*n₂≤L)
    (hhigh : 4*η+τ≤ radialCenter m H θ D B) :
    Z^τ ≤ (Z^m/(d*v^2*n₁*n₂))*hnorm := by
  exact (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)).trans
    (actual_radial_center_lower Z D m B θ H η C d v n₁ n₂ L hnorm
      hZ hd hv hn₁ hn₂ hL hC hdiv hcol hfreq h₁ h₂)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailAnnulus -/

section

namespace OAI

noncomputable section

namespace SevenEighths.InverseInitialHighFrequencyTail
open InverseInitialProfile

theorem actual_annulus_radial_lower
    (Z D m B θ H b C d v n₁ n₂ hnorm : ℝ)
    (hZ : 0<Z) (hb : 0<b) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂)
    (hC : Z^B/4≤C) (hdiv : d≤Z^θ) (hfreq : Z^H/4≤hnorm)
    (h₁ : C*v*n₁≤b*Z^D) (h₂ : C*v*n₂≤b*Z^D) :
    Z^(radialCenter m H θ D B)/(64*b^2) ≤
      (Z^m/(d*v^2*n₁*n₂))*hnorm := by
  have hc : 0<C := (show 0<Z^B/4 by positivity).trans_le hC
  have hh : 0≤hnorm := (show 0≤Z^H/4 by positivity).trans hfreq
  have hscale := correlated_scale_lower (Z^m) C d v n₁ n₂ (b*Z^D)
    (by positivity) hc hd hv hn₁ hn₂ (by positivity) h₁ h₂
  have he : Z^m*(Z^B)^2*Z^H/(Z^θ*(Z^D)^2)=Z^(radialCenter m H θ D B) := by
    simp only [pow_two]
    rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,
      ←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
    congr 1
    unfold radialCenter
    ring
  calc
    _ = Z^m*(Z^B/4)^2*(Z^H/4)/(Z^θ*(b*Z^D)^2) := by
      rw [←he]
      ring
    _ ≤ Z^m*C^2*hnorm/(d*(b*Z^D)^2) := by gcongr
    _ = (Z^m*C^2/(d*(b*Z^D)^2))*hnorm := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale hh

theorem actual_annulus_high_gate
    (Z D m B θ H η τ b C d v n₁ n₂ hnorm : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hb : 0<b) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂)
    (hC : Z^B/4≤C) (hdiv : d≤Z^θ) (hfreq : Z^H/4≤hnorm)
    (h₁ : C*v*n₁≤b*Z^D) (h₂ : C*v*n₂≤b*Z^D)
    (hfixed : 64*b^2≤Z^η) (hhigh : 4*η+τ≤ radialCenter m H θ D B) :
    Z^τ≤(Z^m/(d*v^2*n₁*n₂))*hnorm := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  apply le_trans _ (actual_annulus_radial_lower Z D m B θ H b C d v n₁ n₂ hnorm
    hz hb hd hv hn₁ hn₂ hC hdiv hfreq h₁ h₂)
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    Z^τ*(64*b^2)≤Z^τ*Z^η := mul_le_mul_of_nonneg_left hfixed (by positivity)
    _ = Z^(τ+η) := (Real.rpow_add hz τ η).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailInfinite -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O"=>ActualEisensteinCubic.O

theorem weighted_radial_summable (Φ : 𝓢(ℝ,ℂ)) (K Γ : ℝ) (hK : 0<K)
    (P : O→Prop) (a : O→ℂ) (ha : ∀h,P h→‖a h‖≤Γ) :
    Summable (fun h : {h:O // P h}=>a h.val*paperRadialFourier Φ (K*‖eisEmbedding h.val‖^2)) := by
  apply Summable.of_norm_bounded
    (((paperRadialFourier_lattice_summable_norm Φ K hK).subtype P).mul_left Γ)
  intro h
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ha h.val h.property) (norm_nonneg _)

theorem norm_tsum_of_finite_bound {α : Type*} (f : α→ℂ) (hf : Summable f) (B : ℝ)
    (hb : ∀F : Finset α,‖∑h∈F,f h‖≤B) : ‖∑'h,f h‖≤B := by
  exact le_of_tendsto hf.hasSum.norm (Filter.Eventually.of_forall hb)

theorem weighted_radial_tsum_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (Φ : 𝓢(ℝ,ℂ)) (K T Γ : ℝ), 0<K → 0≤T → 0≤Γ →
    ∀ (P : O→Prop) (a : O→ℂ),
    (∀h,P h→T≤K*‖eisEmbedding h‖^2) → (∀h,P h→‖a h‖≤Γ) →
    ‖∑'h : {h:O // P h},a h.val*paperRadialFourier Φ (K*‖eisEmbedding h.val‖^2)‖≤
      Γ*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/((min 1 K)^2*(1+T)^A) := by
  obtain ⟨s,C,hC,hbound⟩ := finite_radial_tail A
  refine ⟨s,C,hC,?_⟩
  intro Φ K T Γ hK hT hΓ P a htail ha
  apply norm_tsum_of_finite_bound _ (weighted_radial_summable Φ K Γ hK P a ha)
  intro F
  have hi : Function.Injective (fun h : {h:O // P h}=>h.val) := Subtype.val_injective
  have he : (∑h∈F,a h.val*paperRadialFourier Φ (K*‖eisEmbedding h.val‖^2))=
      ∑h∈F.image Subtype.val,a h*paperRadialFourier Φ (K*‖eisEmbedding h‖^2) := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ hh=>hi hh
  rw [he]
  apply hbound Φ K T Γ hK hT hΓ (F.image Subtype.val) a
  · intro h hh
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hh
    exact htail x.val x.property
  · intro h hh
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hh
    exact ha x.val x.property

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailScale -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT InverseInitialProfile
local notation "O"=>ActualEisensteinCubic.O

theorem initial_denominator_bound (C d v n₁ n₂ L : ℝ)
    (hC : 1≤C) (_hd : 0≤d) (hv : 0≤v) (hn₁ : 0≤n₁) (hn₂ : 0≤n₂)
    (hL : 0≤L) (hdL : d≤L) (h₁ : C*v*n₁≤L) (h₂ : C*v*n₂≤L) :
    d*v^2*n₁*n₂≤L^3 := by
  have h₁' : v*n₁≤L := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hv hn₁)]
  have h₂' : v*n₂≤L := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hv hn₂)]
  have hh := mul_le_mul h₁' h₂' (mul_nonneg hv hn₂) hL
  have he := mul_le_mul hdL hh (by positivity) hL
  nlinarith

theorem initial_scalar_bound (Z D m d v n₁ n₂ : ℝ) (hZ : 0<Z)
    (hd : 1≤d) (hv : 1≤v) (hn₁ : 1≤n₁) (hn₂ : 1≤n₂) :
    ‖((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)‖≤Z^(m-D) := by
  have hroot : 1≤Real.sqrt (n₁*n₂) := by
    rw [Real.one_le_sqrt]
    exact one_le_mul_of_one_le_of_one_le hn₁ hn₂
  have hden : 1≤d*v*Real.sqrt (n₁*n₂) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hd hv) hroot
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have h := div_le_self (show 0≤Z^(-D)*Z^m by positivity) hden
  apply h.trans_eq
  rw [←Real.rpow_add hZ]
  congr 1
  ring

theorem physical_frequency_tail_uniform (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
      (Z D m C d v n₁ n₂ L T Γ B₁ B₂ : ℝ),
    0<Z → 1≤C → 1≤d → 1≤v → 1≤n₁ → 1≤n₂ → 1≤L →
    d≤L → C*v*n₁≤L → C*v*n₂≤L → 0≤T → 0≤Γ → 0≤B₁ → 0≤B₂ →
    ‖W₁ (C*v*n₁/Z^D)‖≤B₁ → ‖W₂ (C*v*n₂/Z^D)‖≤B₂ →
    ∀ (F : Finset O) (a : O→ℂ),
    (∀h∈F,T≤(Z^m/(d*v^2*n₁*n₂))*‖eisEmbedding h‖^2) →
    (∀h∈F,‖a h‖≤Γ) →
    ‖∑h∈F,a h*physicalKernel W₁ W₂ Φ Z D m
      ![C,d,v,‖eisEmbedding h‖^2,n₁,n₂]‖ ≤
      Γ*Z^(m-D)*B₁*B₂*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := physical_frequency_tail A
  refine ⟨s,C₀,hC₀,?_⟩
  intro W₁ W₂ Φ Z D m C d v n₁ n₂ L T Γ B₁ B₂ hZ hC hd hv hn₁ hn₂ hL
    hdL h₁ h₂ hT hΓ hB₁ hB₂ hw₁ hw₂ F a hF ha
  have hd0 : 0<d := zero_lt_one.trans_le hd
  have hv0 : 0<v := zero_lt_one.trans_le hv
  have hn₁0 : 0<n₁ := zero_lt_one.trans_le hn₁
  have hn₂0 : 0<n₂ := zero_lt_one.trans_le hn₂
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hden := initial_denominator_bound C d v n₁ n₂ L hC hd0.le hv0.le hn₁0.le hn₂0.le hL0.le hdL h₁ h₂
  have hK : Z^m/L^3≤Z^m/(d*v^2*n₁*n₂) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hscalar := initial_scalar_bound Z D m d v n₁ n₂ hZ hd hv hn₁ hn₂
  apply (hbound W₁ W₂ Φ Z D m C d v n₁ n₂ T Γ hZ hd0 hv0 hn₁0 hn₂0 hT hΓ F a hF ha).trans
  simp only [norm_mul]
  have hnorm : ‖((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)‖*
      ‖W₁ (C*v*n₁/Z^D)‖*‖W₂ (C*v*n₂/Z^D)‖ ≤ Z^(m-D)*B₁*B₂ := by gcongr
  calc
    _ ≤ Γ*(Z^(m-D)*B₁*B₂)*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
      gcongr
    _ = _ := by ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailPower -/

section

namespace OAI

noncomputable section

namespace SevenEighths.InverseInitialHighFrequencyTail

theorem initial_tail_power_cost (A : ℕ) (Z L Lcap m D τ : ℝ)
    (hZ : 1≤Z) (hL : 1≤L) (hcap : 0≤Lcap) (hsize : L≤Z^Lcap)
    (hm : -m≤Lcap) (hmd : m-D≤Lcap) :
    (128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A) ≤
      128^7*Z^(16*Lcap-τ*A) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hl : 0<L := zero_lt_one.trans_le hL
  have hbase : Z^(-4*Lcap)≤ min 1 (Z^m/L^3) := by
    apply le_min
    · exact Real.rpow_le_one_of_one_le_of_nonpos hZ (by linarith)
    · calc
        _ = Z^(-Lcap)/(Z^Lcap)^3 := by
          rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
          congr 1
          norm_num
          ring
        _ ≤ Z^m/L^3 := by
          gcongr ; linarith
  calc
    _ ≤ (128*Z^Lcap)^7*Z^Lcap/((Z^(-4*Lcap))^2*(Z^τ)^A) := by
      gcongr ; linarith
    _ = 128^7*Z^(16*Lcap-τ*A) := by
      rw [mul_pow,←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,
        ←Real.rpow_mul_natCast hz.le]
      rw [mul_assoc,←Real.rpow_add hz,←Real.rpow_add hz,mul_div_assoc,
        ←Real.rpow_sub hz]
      congr 2
      norm_num
      ring

theorem initial_tail_rapid_order (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ A : ℕ, ∀ (Z L m D : ℝ), 1≤Z → 1≤L → 0≤Lcap → L≤Z^Lcap →
      -m≤Lcap → m-D≤Lcap →
      (128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A) ≤
        128^7*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((16*Lcap+saving)/τ)
  refine ⟨A,?_⟩
  intro Z L m D hZ hL hcap hsize hm hmd
  apply (initial_tail_power_cost A Z L Lcap m D τ hZ hL hcap hsize hm hmd).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have h := (div_lt_iff₀ hτ).mp hA
  nlinarith

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailWeights -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialEnergyCallerWeights
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι]

theorem marked_support_norm_bound
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hdis : (slots:Set σ).PairwiseDisjoint lists)
    (ha : ∀i∈slots,∀k∈lists i,‖a i k‖≤1)
    (S : Finset ι) (L : ℝ) (hL : 1≤L) (hS : primeProductNorm p S≤L) :
    ‖primeMark slots lists a S‖≤128*L := by
  have heq : boundedPrimeSupports p S L=S.powerset := by
    apply Finset.filter_eq_self.mpr
    intro U hU
    exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hU)).trans hS
  have hc := boundedPrimeSupports_card p hinj S L hL
  rw [heq,Finset.card_powerset] at hc
  exact (primeMark_norm_le_divisor_count slots lists a S hdis ha).trans (by exact_mod_cast hc)

theorem initialColumn_mark_factor
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (Ψ : O→*ℂ) (j C d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    initialColumn p hp hcop hg Ψ j C d h H S =
      initialColumn p hp hcop hg Ψ j C d h (fun _=>1) S * H S := by
  simp only [initialColumn,mul_one]

theorem initialColumn_mark_norm
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (hΨ : ∀n,‖Ψ n‖≤1)
    (j C d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    ‖initialColumn p hp hcop hg Ψ j C d h H S‖≤‖H S‖ := by
  rw [initialColumn_mark_factor,norm_mul]
  exact (mul_le_mul_of_nonneg_right
    ((initialColumn_norm_le p hp hcop hg hc Ψ j C d h S).trans (hΨ _))
    (norm_nonneg _)).trans_eq (one_mul _)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailSource -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialPhysicalMeasure
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def sourceKey (x : Point ι) : Fin 5→Finset ι :=
  ![x.common,x.divisor,x.overlap,x.left,x.right]

def sourcePoint (k : Fin 5→Finset ι) (h : O) : Point ι :=
  ⟨k 0,k 1,k 2,k 3,k 4,h⟩

omit [DecidableEq ι] in
theorem sourcePoint_key (x : Point ι) : sourcePoint (sourceKey x) x.frequency=x := by
  cases x
  rfl

def sourceKeys (S : Finset (Point ι)) : Finset (Fin 5→Finset ι) := S.image sourceKey

def sourceFrequencies (S : Finset (Point ι)) (k : Fin 5→Finset ι) : Finset O :=
  (S.filter (fun x=>sourceKey x=k)).image Point.frequency

theorem mem_sourceFrequencies (S : Finset (Point ι)) (k : Fin 5→Finset ι) (h : O) :
    h∈sourceFrequencies S k ↔ sourcePoint k h∈S := by
  constructor
  · intro hh
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hh
    obtain ⟨hx,hk⟩ := Finset.mem_filter.mp hx
    rw [←hk,←he,sourcePoint_key]
    exact hx
  · intro hh
    apply Finset.mem_image.mpr
    refine ⟨sourcePoint k h,Finset.mem_filter.mpr ⟨hh,?_⟩,rfl⟩
    funext i
    fin_cases i <;> rfl

theorem source_sum_fibers (S : Finset (Point ι)) (f : Point ι→ℂ) :
    ∑x∈S,f x = ∑k∈sourceKeys S,∑h∈sourceFrequencies S k,f (sourcePoint k h) := by
  rw [←Finset.sum_fiberwise_of_maps_to (s:=S) (t:=sourceKeys S) (g:=sourceKey)
    (fun x hx=>Finset.mem_image.mpr ⟨x,hx,rfl⟩) f]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sourceFrequencies,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [←(Finset.mem_filter.mp hx).2,sourcePoint_key]
  · intro x hx y hy hxy
    have hk := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    rw [←sourcePoint_key x,←sourcePoint_key y,hk,hxy]

theorem sourceKeys_card
    (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (S : Finset (Point ι)) (L : ℝ) (hL : 1≤L)
    (hpool : ∀x∈S,∀i,sourceKey x i⊆pool)
    (hnorm : ∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) :
    ((sourceKeys S).card:ℝ)≤(128*L)^5 := by
  let T := boundedPrimeSupports p pool L
  have hsub : sourceKeys S⊆Fintype.piFinset (fun _ : Fin 5=>T) := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hpool x hx i),hnorm x hx i⟩
  have hc := Finset.card_le_card hsub
  have hcast : ((sourceKeys S).card:ℝ)≤(T.card:ℝ)^5 := by
    exact_mod_cast (by simpa using hc)
  exact hcast.trans (pow_le_pow_left₀ (by positivity)
    (boundedPrimeSupports_card p hinj pool L hL) 5)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailAggregate -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open InverseInitialPhysicalMeasure

theorem original_source_norm_fibers
    {ι ρ : Type*} [DecidableEq ι]
    (S : Finset (Point ι)) (R : Finset ρ) (f : Point ι→ρ→ℂ) (b : ρ→ℝ)
    (hb : ∀k∈sourceKeys S,∀r∈R,
      ‖∑h∈sourceFrequencies S k,f (sourcePoint k h) r‖≤b r) :
    ‖∑x∈S,∑r∈R,f x r‖≤((sourceKeys S).card:ℝ)*(∑r∈R,b r) := by
  rw [source_sum_fibers]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑k∈sourceKeys S,∑r∈R,b r := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.sum_comm]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr=>hb k hk r hr))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailCoefficient -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerWeights InverseInitialProfile InverseInitialKernelBridge InverseInitialRayAttachment
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def originalCoefficient (Ψ : O→*ℂ) (j : O) (mark : Finset ι→ℂ)
    (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  (initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ) *
  star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) x.frequency (fun A=>mark (x.common∪A)) (x.overlap∪x.left)) *
  initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=>mark (x.common∪A)) (x.overlap∪x.right)

include hp hcop hg in
theorem physicalTerm_original_coefficient
    (Ψ : O→*ℂ) (j : O) (mark : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : SchwartzMap ℝ ℂ) (Z D m : ℝ)
    (x : Point ι) (hx : Valid x) (ρ : SecondRayIndex) :
    physicalTerm p hp hcop hg Ψ j mark W₁ W₂ Φ Z D m x ρ =
      originalCoefficient p hp hcop hg Ψ j mark x ρ *
      physicalKernel W₁ W₂ Φ Z D m (coordinates p x) := by
  unfold physicalTerm
  rw [sourceIdeal_union p _ _ hx.overlap_left,sourceIdeal_union p _ _ hx.overlap_right,
    physicalKernel_common_factor]
  rfl

include hp hcop hg in
theorem originalCoefficient_marked_bound
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (hΨ : ∀n,‖Ψ n‖≤1) (j : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hdis : (slots:Set σ).PairwiseDisjoint lists)
    (ha : ∀i∈slots,∀k∈lists i,‖a i k‖≤1)
    (x : Point ι) (ρ : SecondRayIndex) (L : ℝ) (hL : 1≤L)
    (hleft : primeProductNorm p x.common*primeProductNorm p x.overlap*
      primeProductNorm p x.left≤L)
    (hright : primeProductNorm p x.common*primeProductNorm p x.overlap*
      primeProductNorm p x.right≤L) :
    ‖originalCoefficient p hp hcop hg Ψ j (primeMark slots lists a) x ρ‖≤
      ‖secondRayCoefficient ρ‖*(128*L)^2 := by
  have hmark (N : Finset ι)
      (hN : primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p N≤L) :
      ‖primeMark slots lists a (x.common∪(x.overlap∪N))‖≤128*L := by
    apply marked_support_norm_bound p hp hinj slots lists a hdis ha _ L hL
    apply (primeProductNorm_union_le_mul p hp _ _).trans
    apply (mul_le_mul_of_nonneg_left (primeProductNorm_union_le_mul p hp _ _)
      (primeProductNorm_pos p hp _).le).trans
    simpa only [mul_assoc] using hN
  have hl := (initialColumn_mark_norm p hp hcop hg hc (secondRayMinus Ψ ρ)
    (fun n=>(secondRayMinus_norm_le Ψ ρ n).trans (hΨ n)) j (∏i∈x.common,p i)
    (divisor p x) x.frequency (fun A=>primeMark slots lists a (x.common∪A))
    (x.overlap∪x.left)).trans (hmark x.left hleft)
  have hr := (initialColumn_mark_norm p hp hcop hg hc (secondRayPlus Ψ ρ)
    (fun n=>(secondRayPlus_norm_le Ψ ρ n).trans (hΨ n)) j (∏i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=>primeMark slots lists a (x.common∪A))
    (x.overlap∪x.right)).trans (hmark x.right hright)
  have hb := initialBeta_norm_le_one p Ψ hΨ j x.common
  have hm := QuadraticInitialBound.norm_ideal_moebius_le_one (sourceIdeal p x.divisor)
  have hv : ‖supportMobius (fun i=>Ideal.span {p i}) x.overlap‖≤1 :=
    QuadraticInitialBound.norm_ideal_moebius_le_one _
  simp only [originalCoefficient,norm_mul,norm_star]
  calc
    _ ≤ 1*1*1*‖secondRayCoefficient ρ‖*(128*L)*(128*L) := by gcongr
    _ = _ := by ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailFiber -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialKernelBridge InverseInitialProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def keyNorms (p : ι→O) (k : Fin 5→Finset ι) : Fin 5→ℝ :=
  fun i=>primeProductNorm p (k i)

omit [DecidableEq ι] in
theorem coordinates_sourcePoint (p : ι→O) (k : Fin 5→Finset ι) (h : O) :
    coordinates p (sourcePoint k h)=
      ![keyNorms p k 0,keyNorms p k 1,keyNorms p k 2,‖eisEmbedding h‖^2,
        keyNorms p k 3,keyNorms p k 4] := by
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  funext i
  fin_cases i <;> simp [coordinates,sourcePoint,physicalCoordinates,keyNorms,hn]

theorem original_frequency_fiber_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L T Γ B₁ B₂ : ℝ),
    0<Z → 1≤L → 0≤T → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (k : Fin 5→Finset ι) (F : Finset O) (w : Point ι→ℂ) (ρ : SecondRayIndex),
    keyNorms p k 1≤L →
    keyNorms p k 0*keyNorms p k 2*keyNorms p k 3≤L →
    keyNorms p k 0*keyNorms p k 2*keyNorms p k 4≤L →
    (∀h∈F,Valid (sourcePoint k h)) → (∀h∈F,‖w (sourcePoint k h)‖≤Γ) →
    (∀h∈F,T≤(Z^m/(keyNorms p k 1*(keyNorms p k 2)^2*
      keyNorms p k 3*keyNorms p k 4))*‖eisEmbedding h‖^2) →
    ‖∑h∈F,w (sourcePoint k h)*physicalTerm p hp hcop hg Ψ j
      (primeMark slots lists a) W₁ W₂ Φ Z D m (sourcePoint k h) ρ‖ ≤
    (Γ*‖secondRayCoefficient ρ‖*(128*L)^2)*Z^(m-D)*B₁*B₂*
      (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
      ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := physical_frequency_tail_uniform A
  refine ⟨s,C₀,hC₀,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc Ψ hΨ j slots lists a hdis ha
    W₁ W₂ Φ Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ k F w ρ hd hleft hright hvalid hw htail
  have hn (i : Fin 5) : 1≤keyNorms p k i := primeProductNorm_ge_one p hp _
  have he : (∑h∈F,w (sourcePoint k h)*physicalTerm p hp hcop hg Ψ j
      (primeMark slots lists a) W₁ W₂ Φ Z D m (sourcePoint k h) ρ) =
      ∑h∈F,(w (sourcePoint k h)*originalCoefficient p hp hcop hg Ψ j
        (primeMark slots lists a) (sourcePoint k h) ρ)*
        physicalKernel W₁ W₂ Φ Z D m
        ![keyNorms p k 0,keyNorms p k 1,keyNorms p k 2,‖eisEmbedding h‖^2,
          keyNorms p k 3,keyNorms p k 4] := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [physicalTerm_original_coefficient p hp hcop hg Ψ j _ W₁ W₂ Φ Z D m _ (hvalid h hh) ρ,
      coordinates_sourcePoint]
    ring
  rw [he]
  apply hbound W₁ W₂ Φ Z D m (keyNorms p k 0) (keyNorms p k 1)
    (keyNorms p k 2) (keyNorms p k 3) (keyNorms p k 4) L T
    (Γ*‖secondRayCoefficient ρ‖*(128*L)^2) B₁ B₂ hZ (hn 0) (hn 1) (hn 2)
    (hn 3) (hn 4) hL hd hleft hright hT (by positivity) hB₁ hB₂ (hW₁ _) (hW₂ _) F _ htail
  intro h hh
  rw [norm_mul]
  have hc := originalCoefficient_marked_bound p hp hcop hg hinj hc Ψ hΨ j slots lists a
    hdis ha (sourcePoint k h) ρ L hL hleft hright
  calc
    _ ≤ Γ*(‖secondRayCoefficient ρ‖*(128*L)^2) := by gcongr; exact hw h hh
    _ = _ := by ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTail -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
local notation "O"=>ActualEisensteinCubic.O

theorem original_physical_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L T Γ B₁ B₂ : ℝ),
    0<Z → 1≤L → 0≤T → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (pool : Finset ι) (S : Finset (Point ι)) (w : Point ι→ℂ),
    (∀x∈S,Valid x) → (∀x∈S,‖w x‖≤Γ) →
    (∀x∈S,∀i,sourceKey x i⊆pool) →
    (∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤L) →
    (∀x∈S,T≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2) →
    ‖physicalBlock p hp hcop hg S w Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m‖ ≤
      (128*L)^7*Γ*(∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖)*Z^(m-D)*B₁*B₂*
        (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hfiber⟩ := original_frequency_fiber_tail A
  refine ⟨s,C₀,hC₀,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
    Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ pool S w hvalid hw hpool hnorm hleft hright htail
  let R : ℝ := Z^(m-D)*B₁*B₂*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
    ((min 1 (Z^m/L^3))^2*(1+T)^A)
  have hR : 0≤R := by dsimp [R]; positivity
  let B : ℝ := Γ*(128*L)^2*R
  have hB : 0≤B := by dsimp [B]; positivity
  have hkey (k) (hk : k∈sourceKeys S) (ρ : SecondRayIndex) :
      ‖∑h∈sourceFrequencies S k,
        w (sourcePoint k h)*physicalTerm p hp hcop hg Ψ j (primeMark slots lists a)
          W₁ W₂ Φ Z D m (sourcePoint k h) ρ‖ ≤ B*‖secondRayCoefficient ρ‖ := by
    obtain ⟨x,hx,hk'⟩ := Finset.mem_image.mp hk
    have hkN (i) : keyNorms p k i=primeProductNorm p (sourceKey x i) := by rw [←hk'];rfl
    have hf (h) (hh : h∈sourceFrequencies S k) := (mem_sourceFrequencies S k h).mp hh
    have hkl : keyNorms p k 0*keyNorms p k 2*keyNorms p k 3≤L := by
      simpa [←hk',keyNorms,sourceKey] using hleft x hx
    have hkr : keyNorms p k 0*keyNorms p k 2*keyNorms p k 4≤L := by
      simpa [←hk',keyNorms,sourceKey] using hright x hx
    have htailk : ∀h∈sourceFrequencies S k,T≤(Z^m/(keyNorms p k 1*(keyNorms p k 2)^2*
        keyNorms p k 3*keyNorms p k 4))*‖eisEmbedding h‖^2 := by
      intro h hh
      simpa only [sourcePoint,keyNorms] using htail (sourcePoint k h) (hf h hh)
    have hb := hfiber p hp hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
      Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ k (sourceFrequencies S k) w ρ
      (by rw [hkN];exact hnorm x hx 1) hkl hkr
      (fun h hh=>hvalid (sourcePoint k h) (hf h hh))
      (fun h hh=>hw (sourcePoint k h) (hf h hh)) htailk
    apply hb.trans_eq
    dsimp [B,R]
    ring
  have hsum := original_source_norm_fibers S Finset.univ
    (fun x ρ=>w x*physicalTerm p hp hcop hg Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m x ρ)
    (fun ρ=>B*‖secondRayCoefficient ρ‖) (fun k hk ρ _=>hkey k hk ρ)
  change ‖∑x∈S,∑ρ : SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j
    (primeMark slots lists a) W₁ W₂ Φ Z D m x ρ‖≤_
  apply hsum.trans
  rw [←Finset.mul_sum]
  calc
    _ ≤ (128*L)^5*(B*(∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖)) :=
      mul_le_mul_of_nonneg_right (sourceKeys_card p hp hinj pool S L hL hpool hnorm) (by positivity)
    _ = _ := by dsimp [B,R]; ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailRapid -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
local notation "O"=>ActualEisensteinCubic.O

theorem original_physical_tail_rapid (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L Γ B₁ B₂ : ℝ),
    1≤Z → 1≤L → 0≤Lcap → L≤Z^Lcap → -m≤Lcap → m-D≤Lcap → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (pool : Finset ι) (S : Finset (Point ι)) (w : Point ι→ℂ),
    (∀x∈S,Valid x) → (∀x∈S,‖w x‖≤Γ) →
    (∀x∈S,∀i,sourceKey x i⊆pool) →
    (∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤L) →
    (∀x∈S,Z^τ≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2) →
    ‖physicalBlock p hp hcop hg S w Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m‖ ≤
      C₀*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨A,hA⟩ := initial_tail_rapid_order Lcap saving τ hτ
  obtain ⟨s,C₀,hC₀,hraw⟩ := original_physical_tail A
  let R : ℝ := ∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖
  have hR : 0≤R := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  refine ⟨s,128^7*(R+1)*C₀,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
    Z D m L Γ B₁ B₂ hZ hL hcap hsize hm hmd hΓ hB₁ hB₂ hW₁ hW₂ pool S w
    hvalid hw hpool hnorm hleft hright htail
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := hraw p hp hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
    Z D m L (Z^τ) Γ B₁ B₂ hz hL (by positivity) hΓ hB₁ hB₂ hW₁ hW₂
    pool S w hvalid hw hpool hnorm hleft hright htail
  have hs : 0≤ s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ := apply_nonneg _ _
  apply hb.trans
  calc
    _ = ((128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A))*
        (Γ*R*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) := by dsimp [R];ring
    _ ≤ (128^7*Z^(-saving))*(Γ*R*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) :=
      mul_le_mul_of_nonneg_right (hA Z L m D hZ hL hcap hsize hm hmd) (by positivity)
    _ ≤ (128^7*Z^(-saving))*(Γ*(R+1)*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) := by
      gcongr
      linarith
    _ = _ := by ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialProfileBounds -/

section

namespace OAI

noncomputable section

open scoped Classical SchwartzMap
namespace SevenEighths.InverseInitialProfileBounds
open InverseInitialProfile InverseMoment FourierBridge

theorem clipped_norm (W:ℝ→ℂ)(c θ x:ℝ):‖clippedSource W c θ x‖=‖W (c*x)‖:=by
  simp only [clippedSource,norm_mul,logPhase_norm,one_mul]

theorem clipped_bound (W:ℝ→ℂ)(B:ℝ)(hW:∀x,‖W x‖≤B)(c θ x:ℝ):
    ‖clippedSource W c θ x‖≤B:=by rw [clipped_norm];exact hW _

theorem clipped_support (W:ℝ→ℂ)(a b c cmax θ:ℝ)(ha:0<a)(hc:1≤ c)(hcm:c≤ cmax)
    (hW:Function.support W⊆Set.Icc a b):
    Function.support (clippedSource W c θ)⊆Set.Icc (a/cmax) b:=by
  intro x hx
  have hn:W (c*x)≠0:=(mul_ne_zero_iff.mp hx).2
  have hs:=hW hn
  have hcp:0<c:=zero_lt_one.trans_le hc
  have hxpos:0<x:=pos_of_mul_pos_right (ha.trans_le hs.1) hcp.le
  constructor
  · apply (div_le_iff₀ (hcp.trans_le hcm)).mpr
    exact hs.1.trans (by nlinarith)
  · have hxc:x≤ c*x:=le_mul_of_one_le_left hxpos.le hc
    exact hxc.trans hs.2

theorem clipped_support_upper (W:ℝ→ℂ)(a b c θ:ℝ)(ha:0<a)(hc:1≤ c)
    (hW:Function.support W⊆Set.Icc a b):Function.support (clippedSource W c θ)⊆Set.Iic b:=
  fun _ hx=>(clipped_support W a b c c θ ha hc le_rfl hW hx).2

theorem childLogTest_eq_clipped (W:ℝ→ℂ)(θ:ℝ):childLogTest W θ=clippedSource W 1 θ:=by
  funext x
  simp only [childLogTest,clippedSource,mul_comm,mul_one]

theorem childLogTest_norm (W:ℝ→ℂ)(θ x:ℝ):‖childLogTest W θ x‖=‖W x‖:=by
  rw [childLogTest_eq_clipped,clipped_norm,one_mul]

end SevenEighths.InverseInitialProfileBounds

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialQuotientGeometry -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalQuadraticSieve
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialQuotientGeometry

local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)

def sourceWeight {J : ℕ} (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (Z B θ : ℝ) (x : Source (ι:=ι) J) : ℂ :=
  A x * ψC ((Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Z^B) *
    ψd ((Ideal.absNorm (sourceIdeal p x.divisor) : ℝ)/Z^θ)

def retained {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ) : Finset (Source (ι:=ι) J) :=
  S.filter (fun x => sourceWeight p A ψC ψd Z B θ x ≠ 0)

def quotientSet {J : ℕ} (S : Finset (Source (ι:=ι) J)) : Finset (Ideal Eis) :=
  S.image (fun x => sourceIdeal p (x.common\x.divisor))

omit [DecidableEq ι] in
theorem retained_sum {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ)
    (F : Source (ι:=ι) J → ℂ) :
    (∑ x ∈ S, sourceWeight p A ψC ψd Z B θ x * F x) =
      ∑ x ∈ retained p S A ψC ψd Z B θ, sourceWeight p A ψC ψd Z B θ x * F x := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x hx hn
  have hz : sourceWeight p A ψC ψd Z B θ x = 0 := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨hx,h⟩)
  simp [hz]

omit [DecidableEq ι] in

theorem retained_phase_independent {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ)
    (phase : Source (ι:=ι) J → ℂ) (hp : ∀ x ∈ S, phase x ≠ 0) :
    S.filter (fun x => sourceWeight p A ψC ψd Z B θ x * phase x ≠ 0) =
      retained p S A ψC ψd Z B θ := by
  ext x
  simp only [Finset.mem_filter, retained, mul_ne_zero_iff]
  constructor
  · rintro ⟨hx,hw,_⟩
    exact ⟨hx,hw⟩
  · rintro ⟨hx,hw⟩
    exact ⟨hx,hw,hp x hx⟩

variable (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_nonzero {J : ℕ} (S : Finset (Source (ι:=ι) J)) :
    ∀ t ∈ quotientSet p S, t ≠ 0 := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  exact sourceIdeal_ne_zero p hp _

include hp in

theorem quotientSet_eq_initial {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (u : Eisˣ) (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) :
    initialQuotientSet (S.image (fun x => toTuple p (sectorSource u x))) = quotientSet p S := by
  rw [initialQuotientSet, Finset.image_image]
  apply Finset.image_congr
  intro x hx
  change idealQuotient (sourceIdeal p x.divisor) (sourceIdeal p x.common) = _
  exact source_quotient p hp x.common x.divisor (hdiv x hx)

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotient_norm_eq {J : ℕ} (x : Source (ι:=ι) J) (hdiv : x.divisor ⊆ x.common) :
    (Ideal.absNorm (sourceIdeal p (x.common\x.divisor)) : ℝ) =
      (Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Ideal.absNorm (sourceIdeal p x.divisor) := by
  have he : sourceIdeal p x.divisor * sourceIdeal p (x.common\x.divisor) = sourceIdeal p x.common := by
    rw [←sourceIdeal_union p x.divisor (x.common\x.divisor) Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hdiv]
  have hn := congrArg (fun I : Ideal Eis => (Ideal.absNorm I : ℝ)) he
  simp only [map_mul,Nat.cast_mul] at hn
  have hd : (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _)
  apply (eq_div_iff hd).mpr
  simpa only [mul_comm] using hn

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in

theorem retained_norm_windows {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    {x : Source (ι:=ι) J} (hx : x ∈ retained p S A ψC ψd Z B θ) :
    (Ideal.absNorm (sourceIdeal p x.common) : ℝ) ≤ bC*Z^B ∧
      ad*Z^θ ≤ (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) := by
  have hn := (Finset.mem_filter.mp hx).2
  have hnC : ψC ((Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Z^B) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
  have hnd : ψd ((Ideal.absNorm (sourceIdeal p x.divisor) : ℝ)/Z^θ) ≠ 0 :=
    (mul_ne_zero_iff.mp hn).2
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hC hnC).2,
    (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hd hnd).1⟩

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_quotient_bound {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) :
    ∀ t ∈ quotientSet p (retained p S A ψC ψd Z B θ),
      (Ideal.absNorm t : ℝ) ≤ Z^(B-θ+2*η) := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  have hw := retained_norm_windows p S A ψC ψd aC bC ad bd Z B θ hZ hC hd hx
  rw [quotient_norm_eq p hp x (hdiv x (Finset.mem_filter.mp hx).1)]
  have hc : (Ideal.absNorm (sourceIdeal p x.common) : ℝ) ≤ Z^(B+η) := by
    apply (hw.1.trans (mul_le_mul_of_nonneg_right hCup (Real.rpow_pos_of_pos hZ _).le)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  have he : Z^(θ-η) ≤ (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) := by
    apply le_trans _ hw.2
    calc
      _ = Z^(-η)*Z^θ := by rw [←Real.rpow_add hZ]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdlo (Real.rpow_pos_of_pos hZ _).le
  calc
    _ ≤ Z^(B+η)/Z^(θ-η) := div_le_div₀ (by positivity) hc (Real.rpow_pos_of_pos hZ _) he
    _ = _ := by rw [←Real.rpow_sub hZ]; congr 1; ring

theorem endpoint_threshold (bC ad : ℝ) (had : 0 < ad) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧ bC ≤ Z^η ∧ Z^(-η) ≤ ad := by
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop bC),
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop ad⁻¹)] with Z hZ hC hd
  refine ⟨hZ,hC,?_⟩
  rw [Real.rpow_neg (zero_lt_one.trans hZ).le]
  exact (inv_le_comm₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) had).mpr hd

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_empty_iff {J : ℕ} (S : Finset (Source (ι:=ι) J)) :
    quotientSet p S = ∅ ↔ S = ∅ := Finset.image_eq_empty

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_empty_sum {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ)
    (h : quotientSet p (retained p S A ψC ψd Z B θ) = ∅)
    (F : Source (ι:=ι) J → ℂ) :
    (∑ x ∈ S, sourceWeight p A ψC ψd Z B θ x * F x) = 0 := by
  rw [retained_sum p S A ψC ψd Z B θ F, (quotientSet_empty_iff p _).mp h]
  simp

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem nonempty_radius {J : ℕ} (S : Finset (Source (ι:=ι) J)) (Z P η : ℝ)
    (hZ : 1 < Z) (hne : (quotientSet p S).Nonempty)
    (hnorm : ∀ t ∈ quotientSet p S, (Ideal.absNorm t : ℝ) ≤ Z^(P+2*η)) :
    1 ≤ Z^(P+2*η) ∧ 0 ≤ P+2*η := by
  obtain ⟨t,ht⟩ := hne
  have ht0 := quotientSet_nonzero p hp S t ht
  have hn : (1:ℝ) ≤ Ideal.absNorm t := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ht0)
  have hh := hn.trans (hnorm t ht)
  refine ⟨hh,?_⟩
  exact (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero] using hh)

def normalizedMass (J : ℕ) (T : Finset (Ideal Eis)) (H : ℝ) : ℝ :=
  H⁻¹ * ∑ t ∈ T, ((idealDivisors t).card : ℝ)^J

theorem normalized_mass_bound (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (Ideal Eis)) (H : ℝ), 0 < H →
      (∀ t ∈ T, t ≠ 0) → (∀ t ∈ T, (Ideal.absNorm t : ℝ) ≤ H) →
      normalizedMass J T H ≤ C*H^ε := by
  obtain ⟨C,hC,hb⟩ := ideal_divisor_power_small J ε hε
  refine ⟨128*C,by positivity,?_⟩
  intro T H hH hz hn
  rcases T.eq_empty_or_nonempty with he|⟨t,ht⟩
  · subst T
    simp only [normalizedMass,Finset.sum_empty,mul_zero]
    positivity
  have hH1 : 1 ≤ H := by
    have ht1 : (1:ℝ) ≤ Ideal.absNorm t := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hz t ht))
    exact ht1.trans (hn t ht)
  have hw : ∀ t ∈ T, ((idealDivisors t).card : ℝ)^J ≤ C*H^ε := by
    intro t ht
    exact (hb t (hz t ht)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hn t ht) hε.le) hC.le)
  have hs : (∑ t ∈ T, ((idealDivisors t).card : ℝ)^J) ≤ (128*H)*(C*H^ε) := by
    calc
      _ ≤ ∑ _t ∈ T, C*H^ε := Finset.sum_le_sum hw
      _ = (T.card:ℝ)*(C*H^ε) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (DescentFiberCost.finite_ideal_count_real T H hH1 hz hn) (by positivity)
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hH.le)).trans_eq
  field_simp

theorem retained_normalized_mass (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (S : Finset (Source (ι:=ι) J)) (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
      (aC bC ad bd Z B θ η : ℝ), 0 < Z →
      Function.support ψC ⊆ Set.Icc aC bC → Function.support ψd ⊆ Set.Icc ad bd →
      bC ≤ Z^η → Z^(-η) ≤ ad → (∀ x ∈ S, x.divisor ⊆ x.common) →
      Z^(-(B-θ+2*η)) *
        (∑ t ∈ quotientSet p (retained p S A ψC ψd Z B θ), ((idealDivisors t).card : ℝ)^J) ≤
        C*Z^((B-θ+2*η)*ε) := by
  obtain ⟨C,hC,hb⟩ := normalized_mass_bound J ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ S A ψC ψd aC bC ad bd Z B θ η hZ hCw hdw hCup hdlo hdiv
  have h := hb (quotientSet p (retained p S A ψC ψd Z B θ)) (Z^(B-θ+2*η))
    (Real.rpow_pos_of_pos hZ _) (quotientSet_nonzero p hp _)
    (retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η hZ hCw hdw hCup hdlo hdiv)
  simpa only [normalizedMass,←Real.rpow_neg hZ.le,←Real.rpow_mul hZ.le] using h

theorem retained_normalized_mass_pi (J : ℕ) (U π : ℝ) (hU : 0 ≤ U) (hπ : 0 < π) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (S : Finset (Source (ι:=ι) J)) (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
      (aC bC ad bd Z B θ η : ℝ), 1 ≤ Z →
      Function.support ψC ⊆ Set.Icc aC bC → Function.support ψd ⊆ Set.Icc ad bd →
      bC ≤ Z^η → Z^(-η) ≤ ad → (∀ x ∈ S, x.divisor ⊆ x.common) → B-θ+2*η ≤ U →
      Z^(-(B-θ+2*η)) *
        (∑ t ∈ quotientSet p (retained p S A ψC ψd Z B θ), ((idealDivisors t).card : ℝ)^J) ≤ C*Z^π := by
  have hε : 0 < π/(U+1) := div_pos hπ (by linarith)
  obtain ⟨C,hC,hb⟩ := retained_normalized_mass J (π/(U+1)) hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ S A ψC ψd aC bC ad bd Z B θ η hZ hCw hdw hCup hdlo hdiv hcap
  apply (hb p hp S A ψC ψd aC bC ad bd Z B θ η (zero_lt_one.trans_le hZ)
    hCw hdw hCup hdlo hdiv).trans
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ ?_) hC.le
  apply (mul_le_mul_of_nonneg_right hcap hε.le).trans
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by linarith : 0 < U+1)).mpr
  nlinarith

theorem radical_norm_le (I : Ideal Eis) (hI : I ≠ 0) :
    (Ideal.absNorm I.radical : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)

theorem radical_product_bound (t j : Ideal Eis) (ht : t ≠ 0) (hj : j ≠ 0)
    (Z P G η : ℝ) (hZ : 0 < Z)
    (hnt : (Ideal.absNorm t : ℝ) ≤ Z^(P+2*η))
    (hnj : (Ideal.absNorm j : ℝ) ≤ Z^(G+η)) :
    (Ideal.absNorm (t*j).radical : ℝ) ≤ Z^(P+G+3*η) := by
  apply (radical_norm_le (t*j) (mul_ne_zero ht hj)).trans
  simp only [map_mul,Nat.cast_mul]
  calc
    _ ≤ Z^(P+2*η)*Z^(G+η) := mul_le_mul hnt hnj (by positivity) (by positivity)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring

def assignedCenter {σ : Type*} (slots : Finset σ) (z : σ → ℝ) : ℝ := ∑ i ∈ slots, z i

theorem assigned_register {σ : Type*} [DecidableEq σ]
    (all assigned : Finset σ) (ha : assigned ⊆ all) (z : σ → ℝ)
    (hz : ∀ i ∈ all, 0 ≤ z i) :
    0 ≤ assignedCenter assigned z ∧ 0 ≤ assignedCenter (all\assigned) z ∧
      assignedCenter all z - assignedCenter assigned z = assignedCenter (all\assigned) z := by
  refine ⟨Finset.sum_nonneg (fun i hi => hz i (ha hi)),
    Finset.sum_nonneg (fun i hi => hz i (Finset.mem_sdiff.mp hi).1),?_⟩
  unfold assignedCenter
  have h := Finset.sum_sdiff ha (f := z)
  linarith

def assignedElement {σ : Type*} (slots : Finset σ) (q : σ → Eis) : Eis := ∏ i ∈ slots, q i

theorem assigned_norm_bound {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ) (Z : ℝ) (hZ : 0 < Z)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0) :
    (Ideal.absNorm (Ideal.span {assignedElement slots q}) : ℝ) ≤
      (∏ i ∈ slots, b i)*Z^(assignedCenter slots z) := by
  have hb : ∀ i ∈ slots, (Ideal.absNorm (Ideal.span {q i}) : ℝ) ≤ b i*Z^(z i) := by
    intro i hi
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hW i hi (hret i hi)).2
  have hp := Finset.prod_le_prod₀ (fun i _ => (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {q i})))) hb
  simpa only [assignedElement,FiniteGaussPhase.span_finset_prod,map_prod,Nat.cast_prod,
    Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hZ,assignedCenter] using hp

theorem assigned_norm_power {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ) (Z η : ℝ) (hZ : 0 < Z)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ slots, b i) ≤ Z^η) :
    (Ideal.absNorm (Ideal.span {assignedElement slots q}) : ℝ) ≤
      Z^(assignedCenter slots z+η) := by
  apply (assigned_norm_bound slots q z a b W Z hZ hW hret).trans
  calc
    _ ≤ Z^η*Z^(assignedCenter slots z) := mul_le_mul_of_nonneg_right hthreshold (by positivity)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring

include hp in

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_assigned_puncture_bound {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hq : ∀ i ∈ slots, q i ≠ 0)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ slots, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (retained p S A ψC ψd Z B θ)) :
    (Ideal.absNorm (t*Ideal.span {assignedElement slots q}).radical : ℝ) ≤
      Z^((B-θ)+assignedCenter slots z+3*η) := by
  apply radical_product_bound t (Ideal.span {assignedElement slots q})
    (quotientSet_nonzero p hp _ t ht)
    (Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr hq))
    Z (B-θ) (assignedCenter slots z) η hZ
  · exact retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η
      hZ hC hd hCup hdlo hdiv t ht
  · exact assigned_norm_power slots q z a b W Z η hZ hW hret hthreshold

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem span_source_puncture {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (hpr : ∀ i, λ₀^2 ∣ p i-1) (j : Eis)
    {t : Ideal Eis} (ht : t ∈ quotientSet p S) :
    Ideal.span {j*primaryGenerator t} = t*Ideal.span {j} := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  rw [sourceIdeal_gen p hp hpr]
  simp only [sourceIdeal,Ideal.span_singleton_mul_span_singleton,mul_comm]

def punctureLength (Z : ℝ) (t : Ideal Eis) (j : Eis) : ℝ :=
  Real.log (Ideal.absNorm (Ideal.span {j*primaryGenerator t}).radical : ℝ)/Real.log Z

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_puncture_length_bound {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, λ₀^2 ∣ p i-1)
    {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hq : ∀ i ∈ slots, q i ≠ 0)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ slots, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (retained p S A ψC ψd Z B θ)) :
    punctureLength Z t (assignedElement slots q) ≤ (B-θ)+assignedCenter slots z+3*η := by
  have hz := zero_lt_one.trans hZ
  have hbound := retained_assigned_puncture_bound p hp S A ψC ψd aC bC ad bd Z B θ η
    hz hC hd hCup hdlo hdiv slots q z a b W hq hW hret hthreshold ht
  unfold punctureLength
  rw [span_source_puncture p hp _ hpr _ ht]
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  have htn : t*Ideal.span {assignedElement slots q} ≠ 0 := mul_ne_zero
    (quotientSet_nonzero p hp _ t ht)
    (Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr hq))
  have hrn : (t*Ideal.span {assignedElement slots q}).radical ≠ 0 := by
    intro he
    apply htn
    apply le_bot_iff.mp
    simpa only [he,Ideal.zero_eq_bot] using (Ideal.le_radical :
      t*Ideal.span {assignedElement slots q} ≤ (t*Ideal.span {assignedElement slots q}).radical)
  have hpos : (0:ℝ) < Ideal.absNorm (t*Ideal.span {assignedElement slots q}).radical := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hrn)
  have hlog := Real.log_le_log hpos hbound
  simpa only [Real.log_rpow hz] using hlog

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_initial_margins {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, λ₀^2 ∣ p i-1)
    {σ : Type*} [DecidableEq σ] (all assigned : Finset σ) (ha : assigned ⊆ all)
    (q : σ → Eis) (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hz : ∀ i ∈ all, 0 ≤ z i) (hq : ∀ i ∈ assigned, q i ≠ 0)
    (hW : ∀ i ∈ assigned, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ assigned, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ assigned, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (retained p S A ψC ψd Z B θ))
    (m r δ τ c₁ c₂ : ℝ)
    (h₁ : r+2*assignedCenter all z ≤ m-c₁)
    (h₂ : 2*r+8*assignedCenter all z ≤ 3*m-c₂) :
    c₁+δ-9*η-τ ≤
      initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ -
      initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ -
      punctureLength Z t (assignedElement assigned q) - assignedCenter (all\assigned) z ∧
    c₂+4*δ-22*η-3*τ ≤
      4*initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ -
      3*initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ -
      6*assignedCenter (all\assigned) z := by
  have hr := assigned_register all assigned ha z hz
  have hP := (nonempty_radius p hp (retained p S A ψC ψd Z B θ) Z (B-θ) η hZ ⟨t,ht⟩
    (retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η
      (zero_lt_one.trans hZ) hC hd hCup hdlo hdiv)).2
  have hQ := retained_puncture_length_bound p hp S A ψC ψd aC bC ad bd Z B θ η
    hZ hC hd hCup hdlo hdiv hpr assigned q z a b W hq hW hret hthreshold ht
  simpa only [hr.2.2] using initial_margins_sharp (delta:=δ) (tau:=τ)
    h₁ h₂ hr.1 (by linarith : -2*η ≤ B-θ) hQ

theorem all_endpoint_threshold {σ : Type*} (slots : Finset σ) (b : σ → ℝ)
    (bC ad η : ℝ) (had : 0 < ad) (hη : 0 < η) :
    ∀ᶠ Z : ℝ in Filter.atTop,
      1 < Z ∧ bC ≤ Z^η ∧ Z^(-η) ≤ ad ∧ (∏ i ∈ slots, b i) ≤ Z^η := by
  filter_upwards [endpoint_threshold bC ad had η hη,
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop (∏ i ∈ slots,b i))]
      with Z h hprod
  exact ⟨h.1,h.2.1,h.2.2,hprod⟩

include hp in

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_nonempty_radius {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hne : (quotientSet p (retained p S A ψC ψd Z B θ)).Nonempty) :
    1 ≤ Z^((B-θ)+2*η) ∧ 0 ≤ (B-θ)+2*η :=
  nonempty_radius p hp (retained p S A ψC ψd Z B θ) Z (B-θ) η hZ hne
    (retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η
      (zero_lt_one.trans hZ) hC hd hCup hdlo hdiv)

omit [∀ i, (Ideal.span {p i}).IsMaximal] in

theorem assigned_cutoffs_of_term {J : ℕ} (lists : Fin J → Finset ι)
    (a : Fin J → ι → ℂ) (W : Fin J → ℝ → ℂ) (z : Fin J → ℝ)
    (Z : ℝ) (outer : Finset ι) (assigned : Fin J → ι)
    (hterm : assignedTerm lists
      (fun i x => a i x * W i ((Ideal.absNorm (Ideal.span {p x}) : ℝ)/Z^(z i)))
      outer assigned ≠ 0) :
    ∀ i, assigned i ∈ lists i ∧ assigned i ∈ outer ∧
      W i ((Ideal.absNorm (Ideal.span {p (assigned i)}) : ℝ)/Z^(z i)) ≠ 0 := by
  intro i
  have hi := assignedTerm_source lists _ outer assigned hterm i
  have hn := Finset.prod_ne_zero_iff.mp hterm i (Finset.mem_univ i)
  simp only [hi] at hn
  exact ⟨hi.1,hi.2,(mul_ne_zero_iff.mp hn).2⟩

omit [∀ i, (Ideal.span {p i}).IsMaximal] in

theorem retained_assigned_term {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (lists : Fin J → Finset ι) (a : Fin J → ι → ℂ)
    (ψC ψd : ℝ → ℂ) (Z B θ : ℝ) {x : Source (ι:=ι) J}
    (hx : x ∈ retained p S
      (fun y => A y * assignedTerm lists a (y.common∪y.overlap) y.assigned) ψC ψd Z B θ) :
    assignedTerm lists a (x.common∪x.overlap) x.assigned ≠ 0 := by
  have hn := (Finset.mem_filter.mp hx).2
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1).2

end SevenEighths.InverseInitialQuotientGeometry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCaller -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
namespace SevenEighths.InverseInitialEnergyCaller
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_sector_energy {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (lists : Fin J → Finset ι) (a : Fin J → ι → ℂ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hterm : ∀ x ∈ S, assignedTerm lists a (x.common ∪ x.overlap) x.assigned ≠ 0)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (F : InitialChild → ℂ) :
    (∑ x ∈ S, ‖F (initialChild (toTuple p (sectorSource u x)))‖^2) ≤
      ∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) *
          ∑ k ∈ rows, ‖F (t,f,k)‖^2 := by
  let T := S.image (fun x => toTuple p (sectorSource u x))
  have hvalid : ∀ y ∈ T, InitialSourceValid y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact actual_source_valid p hp hpr (sectorSource u x) (hdiv x hx) lists a (hterm x hx)
  have hc : ∀ y ∈ T, (initialChild y).2.1 ∈ labels ∧ (initialChild y).2.2 ∈ rows := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hchild x hx
  have he := initial_energy_projection T hvalid labels rows hlabels hc
    (fun _ => 1) (fun _ _ => le_rfl) F
  simp only [one_mul] at he
  rw [show initialQuotientSet T = quotientSet p S from
    quotientSet_eq_initial p hp S u hdiv] at he
  have hs : (∑ y ∈ T, ‖F (initialChild y)‖^2) =
      ∑ x ∈ S, ‖F (initialChild (toTuple p (sectorSource u x)))‖^2 := by
    exact Finset.sum_image (fun x _ y _ he => sectorSource_injective u (toTuple_injective p hinj he))
  rw [hs] at he
  exact he

include hp in

theorem actual_sector_signed_pair {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (lists : Fin J → Finset ι) (a : Fin J → ι → ℂ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hterm : ∀ x ∈ S, assignedTerm lists a (x.common ∪ x.overlap) x.assigned ≠ 0)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (c : Source (ι:=ι) J → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ x ∈ S, ‖c x‖ ≤ A) (F G : InitialChild → ℂ) :
    ‖∑ x ∈ S, c x * star (F (initialChild (toTuple p (sectorSource u x)))) *
        G (initialChild (toTuple p (sectorSource u x)))‖ ≤
      A * (Real.sqrt (∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) * ∑ k ∈ rows, ‖F (t,f,k)‖^2) *
        Real.sqrt (∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) * ∑ k ∈ rows, ‖G (t,f,k)‖^2)) := by
  let child := fun x : Source (ι:=ι) J => initialChild (toTuple p (sectorSource u x))
  have hF := actual_sector_energy p hp hinj hpr S u lists a hdiv hterm labels rows hlabels hchild F
  have hG := actual_sector_energy p hp hinj hpr S u lists a hdiv hterm labels rows hlabels hchild G
  calc
    _ ≤ ∑ x ∈ S, ‖c x * star (F (child x)) * G (child x)‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ S, A * (‖F (child x)‖ * ‖G (child x)‖) := by
      apply Finset.sum_le_sum
      intro x hx
      simp only [norm_mul, norm_star]
      nlinarith [mul_le_mul_of_nonneg_right (hc x hx)
        (mul_nonneg (norm_nonneg (F (child x))) (norm_nonneg (G (child x))))]
    _ = A * ∑ x ∈ S, ‖F (child x)‖ * ‖G (child x)‖ := by rw [Finset.mul_sum]
    _ ≤ A * (Real.sqrt (∑ x ∈ S, ‖F (child x)‖^2) *
        Real.sqrt (∑ x ∈ S, ‖G (child x)‖^2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt S _ _) hA
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA

end SevenEighths.InverseInitialEnergyCaller

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAssigned -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialEnergyCallerAssigned
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def attach {J : ℕ} (x : Source (ι:=ι) 0) (q : Fin J→ι) : Source (ι:=ι) J where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency
  assigned := q

def erase {J : ℕ} (x : Source (ι:=ι) J) : Source (ι:=ι) 0 where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency
  assigned := Fin.elim0

omit [DecidableEq ι] in
@[simp] theorem erase_attach {J : ℕ} (x : Source (ι:=ι) 0) (q : Fin J→ι) :
    erase (attach x q) = x := by
  apply Source.ext <;> try rfl
  funext i
  exact Fin.elim0 i

omit [DecidableEq ι] in
theorem attach_injective {J : ℕ} :
    Function.Injective (fun z : Source (ι:=ι) 0 × (Fin J→ι) => attach z.1 z.2) := by
  intro x y h
  apply Prod.ext
  · simpa only [erase_attach] using congrArg erase h
  · exact congrArg Source.assigned h

def attachPair (J₁ J₂ : Finset σ)
    (z : Source (ι:=ι) 0 × ((∀ i∈J₁,ι) × (∀ i∈J₂,ι))) :
    Source (ι:=ι) (J₁.card+J₂.card) :=
  attach z.1 (pairedSlotAssignment J₁ J₂ z.2)

omit [DecidableEq ι] [DecidableEq σ] in
theorem attachPair_injective (J₁ J₂ : Finset σ) :
    Function.Injective (attachPair (ι:=ι) J₁ J₂) := by
  intro x y h
  have he := @attach_injective ι (J₁.card + J₂.card)
    (x.1,pairedSlotAssignment J₁ J₂ x.2) (y.1,pairedSlotAssignment J₁ J₂ y.2) h
  exact Prod.ext (congrArg (fun z : Source (ι:=ι) 0 × (Fin (J₁.card+J₂.card)→ι)=>z.1) he)
    (pairedSlotAssignment_injective J₁ J₂
      (congrArg (fun z : Source (ι:=ι) 0 × (Fin (J₁.card+J₂.card)→ι)=>z.2) he))

def assignedSource (S : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ→Finset ι) : Finset (Source (ι:=ι) (J₁.card+J₂.card)) :=
  ((S ×ˢ ((J₁.pi L₁) ×ˢ (J₂.pi L₂))).filter
    (fun z=>∀ i,pairedSlotAssignment J₁ J₂ z.2 i∈z.1.common∪z.1.overlap)).image
      (attachPair J₁ J₂)

def coefficient (J₁ J₂ : Finset σ) (a₁ a₂ : σ→ι→ℂ)
    (x : Source (ι:=ι) (J₁.card+J₂.card)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁
    (fun i hi=>x.assigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩)))) *
    slotAssignmentWeight J₂ a₂
    (fun i hi=>x.assigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩)))

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem coefficient_attach (J₁ J₂ : Finset σ) (a₁ a₂ : σ→ι→ℂ)
    (x : Source (ι:=ι) 0) (q : (∀ i∈J₁,ι) × (∀ i∈J₂,ι)) :
    coefficient J₁ J₂ a₁ a₂ (attachPair J₁ J₂ (x,q)) = pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  simp only [coefficient,attachPair,attach,pairedSlotAssignment,
    Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,pairedSlotWeight]

theorem assignedSource_sum (S : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ→Finset ι) (F : Source (ι:=ι) (J₁.card+J₂.card)→ℂ) :
    ∑ x∈assignedSource S J₁ J₂ L₁ L₂,F x =
      ∑ y∈S,∑ q∈(J₁.pi (fun i=>L₁ i∩(y.common∪y.overlap))) ×ˢ
        (J₂.pi (fun i=>L₂ i∩(y.common∪y.overlap))),F (attachPair J₁ J₂ (y,q)) := by
  rw [assignedSource,Finset.sum_image (fun x _ y _ he=>attachPair_injective J₁ J₂ he),
    Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem original_marks_eq_assigned (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (w P : Source (ι:=ι) 0→ℂ) :
    (∑ y∈S,w y*(star (primeMark J₁ L₁ a₁ (y.common∪y.overlap))*
      primeMark J₂ L₂ a₂ (y.common∪y.overlap))*P y) =
    ∑ x∈assignedSource S J₁ J₂ L₁ L₂,
      (w (erase x)*coefficient J₁ J₂ a₁ a₂ x)*P (erase x) := by
  rw [assignedSource_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [coefficient_attach]
  simp only [attachPair,erase_attach]

theorem assignedSource_support (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι)
    (hdiv : ∀ x∈S,x.divisor⊆x.common)
    {x : Source (ι:=ι) (J₁.card+J₂.card)} (hx : x∈assignedSource S J₁ J₂ L₁ L₂) :
    erase x∈S ∧ x.divisor⊆x.common ∧ ∀ i,x.assigned i∈x.common∪x.overlap := by
  obtain ⟨⟨y,q⟩,hy,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hy
  have hyS := (Finset.mem_product.mp hmem).1
  exact ⟨by simpa only [attachPair,erase_attach] using hyS,hdiv y hyS,hq⟩

theorem coefficient_norm_le_one (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (ha₁ : ∀ i∈J₁,∀ q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂ : ∀ i∈J₂,∀ q∈L₂ i,‖a₂ i q‖≤1)
    {x : Source (ι:=ι) (J₁.card+J₂.card)} (hx : x∈assignedSource S J₁ J₂ L₁ L₂) :
    ‖coefficient J₁ J₂ a₁ a₂ x‖≤1 := by
  obtain ⟨⟨y,q⟩,hy,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hy
  have hq' : q∈(J₁.pi L₁ ×ˢ J₂.pi L₂).filter
      (fun q=>∀ i,pairedSlotAssignment J₁ J₂ q i∈y.common∪y.overlap) :=
    Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hmem).2,hq⟩
  rw [paired_assignment_filter] at hq'
  rw [coefficient_attach]
  exact pairedSlotWeight_norm_le_one J₁ J₂ L₁ L₂ a₁ a₂ _ q hq' ha₁ ha₂

theorem assigned_tuple_valid
    (p : ι→ActualEisensteinCubic.O) (hp : ∀ i,p i≠0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι)
    (hdiv : ∀ x∈S,x.divisor⊆x.common) (u : ActualEisensteinCubic.Oˣ)
    {x : Source (ι:=ι) (J₁.card+J₂.card)} (hx : x∈assignedSource S J₁ J₂ L₁ L₂) :
    InitialSourceValid (toTuple p (sectorSource u x)) := by
  obtain ⟨_,hdivx,hassigned⟩ := assignedSource_support S J₁ J₂ L₁ L₂ hdiv hx
  exact sourceTuple_valid p hp hpr x.common x.divisor x.overlap
    ((u:ActualEisensteinCubic.O)^5*x.frequency) x.assigned hdivx hassigned

end SevenEighths.InverseInitialEnergyCallerAssigned

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerCanonical -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
namespace SevenEighths.InverseInitialEnergyCallerCanonical
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def child (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (c : InitialChild) : ℂ :=
  finiteCanonicalMarkedRow p hp hcop hg pool Ψ (j*primaryGenerator c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a W X

omit [DecidableEq σ] in
theorem energy_eq_normalized (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (J : ℕ) (T : Finset (Ideal Eis))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    {Z : ℝ} (hZ : 0<Z) (F : ℝ) :
    (∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      ∑ f ∈ labels, ((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k ∈ rows, ‖child p hp hcop hg pool Ψ j slots lists a W X (t,f,k)‖^2) =
    Z^F * ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      normalizedColumnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t)
        slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  change ((idealDivisors t).card:ℝ)^J *
    columnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t) slots lists a
      labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X = _
  rw [columnEnergy_normalization p hp hcop hg pool Ψ (j*primaryGenerator t)
    slots lists a labels rows _ W X hZ F]
  ring

omit [DecidableEq σ] in
theorem energy_le_moment (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (J : ℕ) (T : Finset (Ideal Eis))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    {Z : ℝ} (hZ : 0<Z) (F B : ℝ)
    (hmoment : ∀ t ∈ T,
      normalizedColumnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t)
        slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F ≤ B) :
    (∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      ∑ f ∈ labels, ((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k ∈ rows, ‖child p hp hcop hg pool Ψ j slots lists a W X (t,f,k)‖^2) ≤
    (Z^F * ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J) * B := by
  rw [energy_eq_normalized p hp hcop hg pool Ψ j slots lists a W X J T labels rows hZ F,
    mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ.le _)
  exact Finset.sum_le_sum fun t ht =>
    mul_le_mul_of_nonneg_left (hmoment t ht) (by positivity)

theorem sqrt_pair_mass (M B₁ B₂ : ℝ) (hM : 0≤M) :
    Real.sqrt (M*B₁)*Real.sqrt (M*B₂) = M*(Real.sqrt B₁*Real.sqrt B₂) := by
  rw [Real.sqrt_mul hM,Real.sqrt_mul hM]
  calc
    _ = (Real.sqrt M*Real.sqrt M)*(Real.sqrt B₁*Real.sqrt B₂) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hM]

omit [DecidableEq σ] in
theorem signed_canonical_pair_moment {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (assignedLists : Fin J → Finset ι) (assignedCoeff : Fin J → ι → ℂ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hterm : ∀ x ∈ S, assignedTerm assignedLists assignedCoeff
      (x.common ∪ x.overlap) x.assigned ≠ 0)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (c : Source (ι:=ι) J → ℂ) (A : ℝ) (hA : 0≤A)
    (hc : ∀ x ∈ S, ‖c x‖≤A)
    (pool : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (j : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    {Z : ℝ} (hZ : 0<Z) (F B : ℝ) (hB : 0≤B)
    (hmoment₁ : ∀ t ∈ quotientSet p S,
      normalizedColumnEnergy p hp hcop hg pool Ψ₁ (j*primaryGenerator t)
        slots₁ lists₁ a₁ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W₁ X₁ Z F ≤ B)
    (hmoment₂ : ∀ t ∈ quotientSet p S,
      normalizedColumnEnergy p hp hcop hg pool Ψ₂ (j*primaryGenerator t)
        slots₂ lists₂ a₂ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W₂ X₂ Z F ≤ B) :
    ‖∑ x ∈ S, c x *
      star (child p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁
        (initialChild (toTuple p (sectorSource u x)))) *
      child p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂
        (initialChild (toTuple p (sectorSource u x)))‖ ≤
      A * (Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J) * B := by
  have h₁ := energy_le_moment p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁
    J (quotientSet p S) labels rows hZ F B hmoment₁
  have h₂ := energy_le_moment p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂
    J (quotientSet p S) labels rows hZ F B hmoment₂
  apply (InverseInitialEnergyCaller.actual_sector_signed_pair p hp hinj hpr S u
    assignedLists assignedCoeff hdiv hterm labels rows hlabels hchild c A hA hc
    (child p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁)
    (child p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂)).trans
  calc
    _ ≤ A * (Real.sqrt ((Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J)*B) *
        Real.sqrt ((Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J)*B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt h₁)
        (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA
    _ = _ := by
      rw [Real.mul_self_sqrt (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _)
        (Finset.sum_nonneg fun t ht=>by positivity)) hB)]
      ring

end SevenEighths.InverseInitialEnergyCallerCanonical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerFamily -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialEnergyCallerFamily
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem common_killed (G E V : Finset ι) (_hE : E⊆G) (j d t : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∀ i∈G,(j*t)*(d*∏ k∈V,p k)∈Ideal.span {p i} := by
  intro i hi
  by_cases hiE : i∈E
  · have he : d∈Ideal.span {p i} := by
      apply (Ideal.dvd_iff_le.mp (source_prime_dvd p E i hiE))
      rw [←hd]
      exact Ideal.subset_span (Set.mem_singleton d)
    have hh := (Ideal.span {p i}).mul_mem_left ((j*t)*(∏ k∈V,p k)) he
    convert hh using 1 ; ring
  · have hit : i∈G\E := Finset.mem_sdiff.mpr ⟨hi,hiE⟩
    have he : t∈Ideal.span {p i} := by
      apply (Ideal.dvd_iff_le.mp (source_prime_dvd p (G\E) i hit))
      rw [←ht]
      exact Ideal.subset_span (Set.mem_singleton t)
    have hh := (Ideal.span {p i}).mul_mem_left (j*(d*∏ k∈V,p k)) he
    convert hh using 1 ; ring

theorem marked_child_original_lists (F G E V : Finset ι) (hE : E⊆G)
    (Ψ : Eis →* ℂ) (j d t h : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E))
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    (∑ N∈(F\V).powerset,
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>primeMark slots lists a (G∪V∪U)*W (primeProductNorm p (V∪U)/X)) N) =
    ∑ J∈slots.powerset,primeMark J lists a (G∪V)*
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (slots\J) lists a W (X/primeProductNorm p V) := by
  rw [initial_marked_child p hp hcop hg F V G Ψ j t d h slots lists a W X]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteCanonicalMarkedRow_restore_lists p hp hcop hg F G Ψ (j*t)
    (d*∏ i∈V,p i) (d*h) (slots\J) lists a W (X/primeProductNorm p V)
    (common_killed p G E V hE j d t hd ht)]

omit [DecidableEq σ] in
theorem normalized_child_uniform
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (G E V : Finset ι) (d t : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Eisˣ, d=(u:Eis)*primaryGenerator (sourceIdeal p E) ∧
      ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis)
        (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ),
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*primaryGenerator (sourceIdeal p (G\E)))
        (primaryGenerator (sourceIdeal p E*sourceIdeal p V))
        (primaryGenerator (sourceIdeal p E)*((u:Eis)^5*h)) slots lists a W X := by
  have hgen : primaryGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  obtain ⟨u,hu⟩ := generator_eq_unit_primary (sourceIdeal p E) d hd hgen
  refine ⟨u,hu,?_⟩
  intro F Ψ j h slots lists a W X
  obtain ⟨v,hv,hcol⟩ := initial_poisson_child_normalized p hp hcop hg hpr G E V Ψ j d t h hd ht
  have huv : v=u := by
    apply Units.val_injective
    exact mul_right_cancel₀ hgen (hv.symm.trans hu)
  subst v
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro N hN
  exact hcol _ N

theorem fresh_initial_split_fixed_family
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (G E V : Finset ι) (hE : E⊆G) (d t : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Eisˣ, d=(u:Eis)*primaryGenerator (sourceIdeal p E) ∧
      ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis)
        (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ),
      (∑ N∈(F\V).powerset,
        secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
          (fun U=>primeMark slots lists a (G∪V∪U)*W (primeProductNorm p U/X)) N) =
      ∑ J∈slots.powerset,primeMark J lists a (G∪V)*
        finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*primaryGenerator (sourceIdeal p (G\E)))
          (primaryGenerator (sourceIdeal p E*sourceIdeal p V))
          (primaryGenerator (sourceIdeal p E)*((u:Eis)^5*h)) (slots\J) lists a W X := by
  obtain ⟨u,hu,hnorm⟩ := normalized_child_uniform p hp hcop hg hpr G E V d t hd ht (σ:=σ)
  refine ⟨u,hu,?_⟩
  intro F Ψ j h slots lists a W X
  have hV : primeProductNorm p V≠0 := (primeProductNorm_pos p hp V).ne'
  have hx : primeProductNorm p V*X/primeProductNorm p V=X := by
    field_simp
  have he := marked_child_original_lists p hp hcop hg F G E V hE Ψ j d t h hd ht
    slots lists a W (primeProductNorm p V*X)
  rw [hx] at he
  calc
    _ = ∑ N∈(F\V).powerset,
        secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
          (fun U=>primeMark slots lists a (G∪V∪U)*
            W (primeProductNorm p (V∪U)/(primeProductNorm p V*X))) N := by
      apply Finset.sum_congr rfl
      intro N hN
      have hdN : Disjoint V N := Finset.disjoint_left.mpr (by
        intro i hiV hiN
        exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hiN)).2 hiV)
      simp only [secondChildColumn]
      rw [primeProductNorm_union p V N hdN]
      rw [mul_div_mul_left _ _ hV]
    _ = _ := by
      rw [he]
      apply Finset.sum_congr rfl
      intro J hJ
      rw [hnorm F Ψ j h (slots\J) lists a W X]

end SevenEighths.InverseInitialEnergyCallerFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerModes -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialPhysicalMeasure SevenEighths.InverseInitialKernelBridge
open SevenEighths.InverseInitialEnergyCallerFamily SevenEighths.InverseInitialProfile
namespace SevenEighths.InverseInitialEnergyCallerModes
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonicalColumn_marked_sum
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x : Point ι) (hE : x.divisor⊆x.common)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (Z D B v : ℝ) :
    (∑ N∈(F\x.overlap).powerset,
      canonicalColumn p hp hcop hg hpr Ψ j (primeMark slots lists a) x h
        (fun A=>W (columnRatio p A Z D B v)) N) =
      ∑ J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*quotient p x)
          (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
          (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:Eis)^5*h))
          (slots\J) lists a W (Z^(columnCenter D B v)) := by
  have hgen (A : Finset ι) : primaryGenerator (sourceIdeal p A)≠0 := by
    rw [sourceIdeal_gen p hp hpr A]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hd : Ideal.span {primaryGenerator (sourceIdeal p x.divisor)}=sourceIdeal p x.divisor :=
    (primaryGenerator_spec _ (hgen _)).1
  have ht : Ideal.span {quotient p x}=sourceIdeal p (x.common\x.divisor) :=
    (primaryGenerator_spec _ (hgen _)).1
  obtain ⟨u,hu,hsplit⟩ := fresh_initial_split_fixed_family p hp hcop hg hpr
    x.common x.divisor x.overlap hE (primaryGenerator (sourceIdeal p x.divisor))
    (quotient p x) hd ht (σ:=σ)
  have hu1 : u=1 := by
    apply Units.val_injective
    apply mul_right_cancel₀ (hgen x.divisor)
    simpa only [Units.val_one,one_mul] using hu.symm
  subst u
  have he := hsplit F Ψ j ((unitSector p hp hpr x:Eis)^5*h) slots lists a W
    (Z^(columnCenter D B v))
  simp only [Units.val_one,one_pow,one_mul] at he
  convert he using 1
  · apply Finset.sum_congr rfl
    intro N hN
    simp only [canonicalColumn,primaryGenerator_mul,sourceIdeal_gen p hp hpr x.overlap,
      secondChildColumn,columnRatio_actual,Finset.union_assoc]
  · rfl

def sourcePoint (x : Source (ι:=ι) 0) (N M : Finset ι) : Point ι where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  left := N
  right := M
  frequency := x.frequency

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourcePoint_outer_phase (x : Source (ι:=ι) 0) (N M : Finset ι)
    (height : Fin 6→ℝ) (Z D B v θ H : ℝ) :
    secondOuterPhase height (relativeLog (coordinates p (sourcePoint x N M)) Z D B v θ H) =
    secondOuterPhase height (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H) := by
  have hc₀ : coordinates p (sourcePoint x N M) 0=coordinates p (sourcePoint x ∅ ∅) 0 := by
    simp [coordinates,physicalCoordinates,sourcePoint]
  have hc₁ : coordinates p (sourcePoint x N M) 1=coordinates p (sourcePoint x ∅ ∅) 1 := by
    simp [coordinates,physicalCoordinates,sourcePoint]
  have hc₂ : coordinates p (sourcePoint x N M) 2=coordinates p (sourcePoint x ∅ ∅) 2 := by
    simp [coordinates,physicalCoordinates,sourcePoint]
  have hc₃ : coordinates p (sourcePoint x N M) 3=coordinates p (sourcePoint x ∅ ∅) 3 := by
    simp [coordinates,physicalCoordinates,sourcePoint]
  simp [secondOuterPhase,relativeLog,relativeNorm,secondRelativeNorm,hc₀,hc₁,hc₂,hc₃]

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem sourcePoint_unitSector
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x : Source (ι:=ι) 0) (N M : Finset ι) :
    unitSector p hp hpr (sourcePoint x N M)=unitSector p hp hpr (sourcePoint x ∅ ∅) := by
  have hgen : primaryGenerator (sourceIdeal p x.divisor)≠0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  apply Units.val_injective
  apply mul_right_cancel₀ hgen
  exact (unitSector_spec p hp hpr (sourcePoint x N M)).symm.trans
    (unitSector_spec p hp hpr (sourcePoint x ∅ ∅))

def markedModeColumn (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis) (x : Source (ι:=ι) 0)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (Z D B v : ℝ) : ℂ :=
  ∑ J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
    finiteCanonicalMarkedRow p hp hcop hg F Ψ
      (j*quotient p (sourcePoint x ∅ ∅))
      (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
      (primaryGenerator (sourceIdeal p x.divisor)*
        ((unitSector p hp hpr (sourcePoint x ∅ ∅):Eis)^5*h))
      (slots\J) lists a W (Z^(columnCenter D B v))

theorem canonicalPairMode_rectangle
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x : Source (ι:=ι) 0) (hE : x.divisor⊆x.common)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ) (ρ : SecondRayIndex)
    (z : JointLogSeparation.Frequency × (Fin 6→ℝ)) :
    let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
    (∑ N∈(F\x.overlap).powerset,∑ M∈(F\x.overlap).powerset,
      canonicalPairMode p hp hcop hg hpr Ψ j (primeMark slots lists a) ω₁ ω₂
        Z D B v θ H (sourcePoint x N M) ρ z) =
    (outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ *
      secondOuterPhase height (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H)) *
    (star (markedModeColumn p hp hcop hg hpr F (secondRayMinus Ψ ρ) j x.frequency x
        slots lists a (childLogTest ω₁ (-height 4)) Z D B v) *
      markedModeColumn p hp hcop hg hpr F (secondRayPlus Ψ ρ) j (-x.frequency) x
        slots lists a (childLogTest ω₂ (height 5)) Z D B v) := by
  dsimp only
  let x₀ := sourcePoint x ∅ ∅
  have hpoint (N M : Finset ι) :
      canonicalPairMode p hp hcop hg hpr Ψ j (primeMark slots lists a) ω₁ ω₂
        Z D B v θ H (sourcePoint x N M) ρ z =
      (outerCoefficient p hp hcop hg Ψ j x₀ ρ *
        secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2)
          (relativeLog (coordinates p x₀) Z D B v θ H)) *
      star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j (primeMark slots lists a) x₀ x.frequency
        (fun A=>childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4)
          (columnRatio p A Z D B v)) N) *
      canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j (primeMark slots lists a) x₀ (-x.frequency)
        (fun A=>childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5)
          (columnRatio p A Z D B v)) M := by
    unfold InverseInitialPhysicalMeasure.canonicalPairMode
    dsimp only
    rw [sourcePoint_outer_phase p x N M
      (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) Z D B v θ H]
    simp only [canonicalColumn]
    simp only [sourcePoint_unitSector p hp hpr x N M]
    simp only [outerCoefficient,sourcePoint,divisor,quotient,x₀]
  simp_rw [hpoint,←Finset.mul_sum]
  rw [←Finset.sum_mul,←Finset.mul_sum,←star_sum]
  have hleft := canonicalColumn_marked_sum p hp hcop hg hpr x₀ hE F (secondRayMinus Ψ ρ) j x.frequency
      slots lists a (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4)) Z D B v
  have hright := canonicalColumn_marked_sum p hp hcop hg hpr x₀ hE F (secondRayPlus Ψ ρ) j (-x.frequency)
      slots lists a (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5)) Z D B v
  dsimp only [x₀,sourcePoint] at hleft hright ⊢
  rw [hleft,hright]
  simp only [markedModeColumn,sourcePoint]
  ring

end SevenEighths.InverseInitialEnergyCallerModes

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerOpposite -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
open SevenEighths.InverseInitialEnergyCallerCanonical
namespace SevenEighths.InverseInitialEnergyCallerOpposite
local notation "Eis" => ActualEisensteinCubic.O

def negativeChild (c : InitialChild) : InitialChild := (c.1,c.2.1,-c.2.2)

theorem energy_neg_rows (T labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hneg : ∀ k∈rows,-k∈rows) (J : ℕ) (F : InitialChild→ℂ) :
    (∑ t∈T,((idealDivisors t).card:ℝ)^J *
      ∑ f∈labels,((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k∈rows,‖F (negativeChild (t,f,k))‖^2) =
    ∑ t∈T,((idealDivisors t).card:ℝ)^J *
      ∑ f∈labels,((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k∈rows,‖F (t,f,k)‖^2 := by
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  apply Finset.sum_congr rfl
  intro f hf
  congr 1
  apply Finset.sum_bij (fun k _=>-k)
  · exact hneg
  · intro a ha b hb he
    exact neg_injective he
  · intro b hb
    exact ⟨-b,hneg b hb,neg_neg b⟩
  · intro k hk
    rfl

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem signed_opposite_pair_moment {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (assignedLists : Fin J → Finset ι) (assignedCoeff : Fin J → ι → ℂ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hterm : ∀ x ∈ S, assignedTerm assignedLists assignedCoeff
      (x.common ∪ x.overlap) x.assigned ≠ 0)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hneg : ∀ k∈rows,-k∈rows)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (c : Source (ι:=ι) J → ℂ) (A : ℝ) (hA : 0≤A)
    (hc : ∀ x ∈ S, ‖c x‖≤A)
    (pool : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (j : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    {Z : ℝ} (hZ : 0<Z) (F B : ℝ) (hB : 0≤B)
    (hmoment₁ : ∀ t ∈ quotientSet p S,
      normalizedColumnEnergy p hp hcop hg pool Ψ₁ (j*primaryGenerator t)
        slots₁ lists₁ a₁ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W₁ X₁ Z F ≤ B)
    (hmoment₂ : ∀ t ∈ quotientSet p S,
      normalizedColumnEnergy p hp hcop hg pool Ψ₂ (j*primaryGenerator t)
        slots₂ lists₂ a₂ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W₂ X₂ Z F ≤ B) :
    ‖∑ x ∈ S, c x *
      star (child p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁
        (initialChild (toTuple p (sectorSource u x)))) *
      child p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂
        (negativeChild (initialChild (toTuple p (sectorSource u x))))‖ ≤
      A * (Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J) * B := by
  have h₁ := energy_le_moment p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁
    J (quotientSet p S) labels rows hZ F B hmoment₁
  have h₂ := energy_le_moment p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂
    J (quotientSet p S) labels rows hZ F B hmoment₂
  have h₂neg := h₂
  rw [← energy_neg_rows (quotientSet p S) labels rows hneg J
    (child p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂)] at h₂neg
  apply (InverseInitialEnergyCaller.actual_sector_signed_pair p hp hinj hpr S u
    assignedLists assignedCoeff hdiv hterm labels rows hlabels hchild c A hA hc
    (child p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁)
    (fun c=>child p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂ (negativeChild c))).trans
  calc
    _ ≤ A * (Real.sqrt ((Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J)*B) *
        Real.sqrt ((Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J)*B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt h₁)
        (Real.sqrt_le_sqrt h₂neg) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA
    _ = _ := by
      rw [Real.mul_self_sqrt (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _)
        (Finset.sum_nonneg fun t ht=>by positivity)) hB)]
      ring

end SevenEighths.InverseInitialEnergyCallerOpposite

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSource -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open SevenEighths.InverseMoment SevenEighths.InverseInitialProfile
open SevenEighths.InverseInitialArithmetic SevenEighths.InverseInitialPhysicalMeasure
open SevenEighths.InverseInitialEnergyCallerModes
namespace SevenEighths.InverseInitialEnergyCallerSource
variable {ι : Type*} [DecidableEq ι]

def erasePoint (x : Point ι) : Source (ι:=ι) 0 where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency
  assigned := Fin.elim0

omit [DecidableEq ι] in
@[simp] theorem erase_sourcePoint (x : Source (ι:=ι) 0) (N M : Finset ι) :
    erasePoint (sourcePoint x N M)=x := by
  apply Source.ext <;> try rfl
  funext i
  exact Fin.elim0 i

omit [DecidableEq ι] in
theorem point_pair_injective (x : Source (ι:=ι) 0) :
    Function.Injective (fun q : Finset ι × Finset ι=>sourcePoint x q.1 q.2) := by
  intro q r h
  exact Prod.ext (congrArg Point.left h) (congrArg Point.right h)

def rectangle (F : Finset ι) (x : Source (ι:=ι) 0) : Finset (Point ι) :=
  ((F\x.overlap).powerset ×ˢ (F\x.overlap).powerset).image
    (fun q=>sourcePoint x q.1 q.2)

def pointSource (F : Finset ι) (S : Finset (Source (ι:=ι) 0)) : Finset (Point ι) :=
  S.biUnion (rectangle F)

theorem rectangles_disjoint (F : Finset ι) {x y : Source (ι:=ι) 0} (hne : x≠y) :
    Disjoint (rectangle F x) (rectangle F y) := by
  apply Finset.disjoint_left.mpr
  intro z hz₁ hz₂
  obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hz₁
  obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hz₂
  have he := congrArg erasePoint (hea.trans heb.symm)
  simp only [erase_sourcePoint] at he
  exact hne he

theorem pointSource_sum {A : Type*} [AddCommMonoid A]
    (F : Finset ι) (S : Finset (Source (ι:=ι) 0)) (f : Point ι→A) :
    (∑ x∈pointSource F S,f x) =
      ∑ y∈S,∑ N∈(F\y.overlap).powerset,∑ M∈(F\y.overlap).powerset,
        f (sourcePoint y N M) := by
  rw [pointSource,Finset.sum_biUnion (fun x hx y hy hne=>rectangles_disjoint F hne)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [rectangle,Finset.sum_image (fun x _ z _ he=>point_pair_injective y he),Finset.sum_product]

theorem pointSource_valid (F : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hdiv : ∀ x∈S,x.divisor⊆x.common)
    (hfreq : ∀ x∈S,x.frequency≠0) : ∀ y∈pointSource F S,Valid y := by
  intro y hy
  obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hy
  have hd (U : Finset ι) (hU : U∈(F\x.overlap).powerset) : Disjoint x.overlap U := by
    apply Finset.disjoint_left.mpr
    intro i hi hiU
    exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hU hiU)).2 hi
  exact ⟨hdiv x hx,hd N (Finset.mem_product.mp hNM).1,
    hd M (Finset.mem_product.mp hNM).2,hfreq x hx⟩

variable {σ : Type*} [DecidableEq σ]
  (p : ι→ActualEisensteinCubic.O) (hp : ∀ i,p i≠0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def rowMode (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (j : ActualEisensteinCubic.O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (x : Source (ι:=ι) 0) (ρ : SecondRayIndex)
    (z : JointLogSeparation.Frequency × (Fin 6→ℝ)) : ℂ :=
  let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  (outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ *
    secondOuterPhase height (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H)) *
  (star (markedModeColumn p hp hcop hg hpr F (secondRayMinus Ψ ρ) j x.frequency x
      slots lists a (childLogTest ω₁ (-height 4)) Z D B v) *
    markedModeColumn p hp hcop hg hpr F (secondRayPlus Ψ ρ) j (-x.frequency) x
      slots lists a (childLogTest ω₂ (height 5)) Z D B v)

theorem canonicalBlock_rows
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hE : ∀ x∈S,x.divisor⊆x.common) (w : Source (ι:=ι) 0→ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (j : ActualEisensteinCubic.O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (z : JointLogSeparation.Frequency × (Fin 6→ℝ)) :
    canonicalBlock p hp hcop hg hpr (pointSource F S) (w ∘ erasePoint) Ψ j
      (primeMark slots lists a) ω₁ ω₂ Z D B v θ H z =
      ∑ x∈S,∑ ρ : SecondRayIndex,w x*rowMode p hp hcop hg hpr F Ψ j
        slots lists a ω₁ ω₂ Z D B v θ H x ρ z := by
  unfold canonicalBlock
  rw [pointSource_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Function.comp_apply,erase_sourcePoint]
  calc
    _ = ∑ N∈(F\x.overlap).powerset,∑ ρ : SecondRayIndex,∑ M∈(F\x.overlap).powerset,
        w x*InverseInitialPhysicalMeasure.canonicalPairMode p hp hcop hg hpr Ψ j
          (primeMark slots lists a) ω₁ ω₂ Z D B v θ H (sourcePoint x N M) ρ z := by
      apply Finset.sum_congr rfl
      intro N hN
      exact Finset.sum_comm
    _ = ∑ ρ : SecondRayIndex,∑ N∈(F\x.overlap).powerset,∑ M∈(F\x.overlap).powerset,
        w x*InverseInitialPhysicalMeasure.canonicalPairMode p hp hcop hg hpr Ψ j
          (primeMark slots lists a) ω₁ ω₂ Z D B v θ H (sourcePoint x N M) ρ z := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      simp_rw [←Finset.mul_sum]
      rw [canonicalPairMode_rectangle p hp hcop hg hpr x (hE x hx) F Ψ j
        slots lists a ω₁ ω₂ Z D B v θ H ρ z]
      rfl

theorem physicalBlock_rectangular_common_measure
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6→ℝ→ℂ)
    (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ)
    (hid : PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂)
    (F : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hE : ∀ x∈S,x.divisor⊆x.common) (hf : ∀ x∈S,x.frequency≠0)
    (w : Source (ι:=ι) 0→ℂ) (Ψ : ActualEisensteinCubic.O →* ℂ) (j : ActualEisensteinCubic.O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (ω₁ ω₂ : ℝ→ℂ)
    (hsupport : BlockSupport p (pointSource F S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂) :
    physicalBlock p hp hcop hg (pointSource F S) (w ∘ erasePoint) Ψ j (primeMark slots lists a)
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
    (Z^(prefactorCenter m D B θ+3*η):ℝ)*
      ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
        (∑ x∈S,∑ ρ : SecondRayIndex,w x*rowMode p hp hcop hg hpr F Ψ j
          slots lists a ω₁ ω₂ Z D B v θ H x ρ z) := by
  rw [physicalBlock_integral p hp hcop hg hpr W₁ W₂ Φ V g g₁ g₂ b₃
    Z D B v m θ H η c₁ c₂ θ₁ θ₂ hid (pointSource F S) (pointSource_valid F S hE hf)
    (w ∘ erasePoint) Ψ j (primeMark slots lists a) ω₁ ω₂
    hsupport.1 hsupport.2.1 hsupport.2.2]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [canonicalBlock_rows p hp hcop hg hpr F S hE w Ψ j slots lists a ω₁ ω₂ Z D B v θ H z]

end SevenEighths.InverseInitialEnergyCallerSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSupport -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
namespace SevenEighths.InverseInitialEnergyCallerSupport
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_sector_energy {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hsupport : ∀ x ∈ S, ∀i,x.assigned i∈x.common∪x.overlap)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (F : InitialChild → ℂ) :
    (∑ x ∈ S, ‖F (initialChild (toTuple p (sectorSource u x)))‖^2) ≤
      ∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) *
          ∑ k ∈ rows, ‖F (t,f,k)‖^2 := by
  let T := S.image (fun x => toTuple p (sectorSource u x))
  have hvalid : ∀ y ∈ T, InitialSourceValid y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact sourceTuple_valid p hp hpr x.common x.divisor x.overlap
      ((u:Eis)^5*x.frequency) x.assigned (hdiv x hx) (hsupport x hx)
  have hc : ∀ y ∈ T, (initialChild y).2.1 ∈ labels ∧ (initialChild y).2.2 ∈ rows := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hchild x hx
  have he := initial_energy_projection T hvalid labels rows hlabels hc
    (fun _ => 1) (fun _ _ => le_rfl) F
  simp only [one_mul] at he
  rw [show initialQuotientSet T = quotientSet p S from
    quotientSet_eq_initial p hp S u hdiv] at he
  have hs : (∑ y ∈ T, ‖F (initialChild y)‖^2) =
      ∑ x ∈ S, ‖F (initialChild (toTuple p (sectorSource u x)))‖^2 := by
    exact Finset.sum_image (fun x _ y _ he => sectorSource_injective u (toTuple_injective p hinj he))
  rw [hs] at he
  exact he

include hp in

theorem actual_sector_signed_pair {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hsupport : ∀ x ∈ S, ∀i,x.assigned i∈x.common∪x.overlap)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (c : Source (ι:=ι) J → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ x ∈ S, ‖c x‖ ≤ A) (F G : InitialChild → ℂ) :
    ‖∑ x ∈ S, c x * star (F (initialChild (toTuple p (sectorSource u x)))) *
        G (initialChild (toTuple p (sectorSource u x)))‖ ≤
      A * (Real.sqrt (∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) * ∑ k ∈ rows, ‖F (t,f,k)‖^2) *
        Real.sqrt (∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) * ∑ k ∈ rows, ‖G (t,f,k)‖^2)) := by
  let child := fun x : Source (ι:=ι) J => initialChild (toTuple p (sectorSource u x))
  have hF := actual_sector_energy p hp hinj hpr S u hdiv hsupport labels rows hlabels hchild F
  have hG := actual_sector_energy p hp hinj hpr S u hdiv hsupport labels rows hlabels hchild G
  calc
    _ ≤ ∑ x ∈ S, ‖c x * star (F (child x)) * G (child x)‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ S, A * (‖F (child x)‖ * ‖G (child x)‖) := by
      apply Finset.sum_le_sum
      intro x hx
      simp only [norm_mul, norm_star]
      nlinarith [mul_le_mul_of_nonneg_right (hc x hx)
        (mul_nonneg (norm_nonneg (F (child x))) (norm_nonneg (G (child x))))]
    _ = A * ∑ x ∈ S, ‖F (child x)‖ * ‖G (child x)‖ := by rw [Finset.mul_sum]
    _ ≤ A * (Real.sqrt (∑ x ∈ S, ‖F (child x)‖^2) *
        Real.sqrt (∑ x ∈ S, ‖G (child x)‖^2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt S _ _) hA
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA

end SevenEighths.InverseInitialEnergyCallerSupport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAssignedPair -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerAssignedPair
open InverseMoment InverseInitialArithmetic InverseInitialQuotientGeometry
open InverseInitialEnergyCallerAssigned InverseInitialEnergyCallerOpposite
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] in
theorem child_erase {J:ℕ}(u:Eisˣ)(x:Source (ι:=ι) J) :
    initialChild (toTuple p (sectorSource u (erase x)))=
      initialChild (toTuple p (sectorSource u x)) := rfl

include hp in

theorem original_assigned_pair
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)
    (J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)(a₁ a₂:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂:∀i∈J₂,∀q∈L₂ i,‖a₂ i q‖≤1)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (c:Source (ι:=ι) 0→ℂ)(A:ℝ)(hA:0≤A)(hc:∀x∈S,‖c x‖≤A)
    (F G:InitialChild→ℂ) :
    ‖∑x∈S,c x*(star (primeMark J₁ L₁ a₁ (x.common∪x.overlap))*
      primeMark J₂ L₂ a₂ (x.common∪x.overlap))*
      (star (F (initialChild (toTuple p (sectorSource u x))))*
        G (initialChild (toTuple p (sectorSource u x))))‖≤
      A*(Real.sqrt (∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card)*
        ∑f∈labels,((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1)*
          ∑k∈rows,‖F (t,f,k)‖^2)*
        Real.sqrt (∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card)*
        ∑f∈labels,((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1)*
          ∑k∈rows,‖G (t,f,k)‖^2)) := by
  let T := assignedSource S J₁ J₂ L₁ L₂
  have hs (x:Source (ι:=ι) (J₁.card+J₂.card))(hx:x∈T) :=
    assignedSource_support S J₁ J₂ L₁ L₂ hdiv hx
  have hcoeff (x:Source (ι:=ι) (J₁.card+J₂.card))(hx:x∈T) :
      ‖c (erase x)*coefficient J₁ J₂ a₁ a₂ x‖≤A := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (coefficient_norm_le_one S J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ hx)
      (norm_nonneg _)).trans (by simpa only [mul_one] using hc (erase x) (hs x hx).1)
  rw [original_marks_eq_assigned S J₁ J₂ L₁ L₂ a₁ a₂ c
    (fun x=>star (F (initialChild (toTuple p (sectorSource u x))))*
      G (initialChild (toTuple p (sectorSource u x))))]
  simp only [child_erase,←mul_assoc]
  simpa only [←mul_assoc] using InverseInitialEnergyCallerSupport.actual_sector_signed_pair p hp hinj hpr T u
    (fun x hx=>(hs x hx).2.1) (fun x hx=>(hs x hx).2.2) labels rows hlabels
    (fun x hx=>by simpa only [child_erase] using hchild (erase x) (hs x hx).1)
    (fun x=>c (erase x)*coefficient J₁ J₂ a₁ a₂ x) A hA hcoeff F G

end SevenEighths.InverseInitialEnergyCallerAssignedPair

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAssignedCanonical -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerAssignedCanonical
open InverseMoment InverseInitialArithmetic InverseInitialQuotientGeometry
open InverseInitialEnergyCallerAssigned InverseInitialEnergyCallerOpposite
open InverseInitialEnergyCallerCanonical InverseInitialClippedColumns
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_assigned_canonical_pair
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)
    (J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)(a₁ a₂:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂:∀i∈J₂,∀q∈L₂ i,‖a₂ i q‖≤1)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)(hneg:∀k∈rows,-k∈rows)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (c:Source (ι:=ι) 0→ℂ)(A:ℝ)(hA:0≤A)(hc:∀x∈S,‖c x‖≤A)
    (pool:Finset ι)(Ψ₁ Ψ₂:Eis→*ℂ)(j:Eis)(slots₁ slots₂:Finset σ)
    (W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ){Z:ℝ}(hZ:0<Z)(F B₁ B₂:ℝ)
    (hmoment₁:∀t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
      normalizedColumnEnergy p hp hcop hg pool Ψ₁ (j*primaryGenerator t)
        slots₁ L₁ a₁ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        W₁ X₁ Z F≤B₁)
    (hmoment₂:∀t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
      normalizedColumnEnergy p hp hcop hg pool Ψ₂ (j*primaryGenerator t)
        slots₂ L₂ a₂ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        W₂ X₂ Z F≤B₂) :
    ‖∑x∈S,c x*(star (primeMark J₁ L₁ a₁ (x.common∪x.overlap))*
      primeMark J₂ L₂ a₂ (x.common∪x.overlap))*
      (star (child p hp hcop hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
          (initialChild (toTuple p (sectorSource u x))))*
        child p hp hcop hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
          (negativeChild (initialChild (toTuple p (sectorSource u x)))))‖≤
      A*(Z^F*∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*(Real.sqrt B₁*Real.sqrt B₂) := by
  let T := quotientSet p (assignedSource S J₁ J₂ L₁ L₂)
  let f := child p hp hcop hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
  let g := child p hp hcop hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
  have h₁ := energy_le_moment p hp hcop hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
    (J₁.card+J₂.card) T labels rows hZ F B₁ hmoment₁
  have h₂ := energy_le_moment p hp hcop hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
    (J₁.card+J₂.card) T labels rows hZ F B₂ hmoment₂
  rw [←energy_neg_rows T labels rows hneg (J₁.card+J₂.card) g] at h₂
  have hh := InverseInitialEnergyCallerAssignedPair.original_assigned_pair p hp hinj hpr
    S u J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ hdiv labels rows hlabels hchild c A hA hc f
    (fun k=>g (negativeChild k))
  apply hh.trans
  calc
    _≤A*(Real.sqrt ((Z^F*∑t∈T,((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*B₁)*
      Real.sqrt ((Z^F*∑t∈T,((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*B₂)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt h₁)
        (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA
    _=_ := by
      rw [sqrt_pair_mass _ B₁ B₂ (mul_nonneg (Real.rpow_nonneg hZ.le _)
        (Finset.sum_nonneg fun t ht=>by positivity))]
      ring

end SevenEighths.InverseInitialEnergyCallerAssignedCanonical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerMass -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerMass
open InverseMoment InverseInitialArithmetic InverseInitialQuotientGeometry
open InverseInitialEnergyCallerAssigned
local notation "Eis"=>ActualEisensteinCubic.O

theorem assigned_quotient_subset {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→Eis)(S:Finset (Source (ι:=ι) 0))(J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι) :
    quotientSet p (assignedSource S J₁ J₂ L₁ L₂)⊆quotientSet p S := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨⟨y,q⟩,hy,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y,(Finset.mem_product.mp (Finset.mem_filter.mp hy).1).1,rfl⟩

theorem divisor_weight_mono {t:Ideal Eis}(ht:t≠0){J K:ℕ}(hJK:J≤K) :
    ((idealDivisors t).card:ℝ)^J≤((idealDivisors t).card:ℝ)^K := by
  have hc : (1:ℝ)≤(idealDivisors t).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1,(mem_idealDivisors ht).mpr (one_dvd t)⟩
  exact pow_le_pow_right₀ hc hJK

theorem assigned_quotient_mass (K:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (S:Finset (Source (ι:=ι) 0))(J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)
      (_hJ:J₁.card+J₂.card≤K)(Z R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R),
      (∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))≤C*Z^(R+π) := by
  have hε : 0<π/(U+1) := div_pos hπ (by linarith)
  obtain ⟨C,hC,hb⟩ := normalized_mass_bound K (π/(U+1)) hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ S J₁ J₂ L₁ L₂ hJ Z R hZ hR hn
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  let T := quotientSet p (assignedSource S J₁ J₂ L₁ L₂)
  have ht : ∀t∈T,t≠0 := quotientSet_nonzero p hp _
  have hnorm : ∀t∈T,(t.absNorm:ℝ)≤Z^R :=
    fun t hh=>hn t (assigned_quotient_subset p S J₁ J₂ L₁ L₂ hh)
  have hm := hb T (Z^R) (Real.rpow_pos_of_pos hZp _) ht hnorm
  have hpow : (Z^R)^(π/(U+1))≤Z^π := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    apply (mul_le_mul_of_nonneg_right hR hε.le).trans
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<U+1)).mpr
    nlinarith
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hpow hC.le)
  have hs := mul_le_mul_of_nonneg_left hm' (Real.rpow_nonneg hZp.le R)
  simp only [normalizedMass,←mul_assoc,mul_inv_cancel₀ (Real.rpow_pos_of_pos hZp R).ne',one_mul] at hs
  calc
    _≤∑t∈T,((idealDivisors t).card:ℝ)^K :=
      Finset.sum_le_sum fun t hmem=>divisor_weight_mono (ht t hmem) hJ
    _≤Z^R*(C*Z^π) := by simpa only [mul_assoc] using hs
    _=C*Z^(R+π) := by rw [Real.rpow_add hZp];ring

end SevenEighths.InverseInitialEnergyCallerMass

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSector -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerSector
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem markedModeColumn_sector
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Z D B v:ℝ) :
    markedModeColumn p hp hcop hg hpr pool Ψ j x.frequency x slots lists a W Z D B v=
      ∑J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        child p hp hcop hg pool Ψ j (slots\J) lists a W (Z^(columnCenter D B v))
          (initialChild (toTuple p (sectorSource u x))) := by
  unfold markedModeColumn
  rw [hu]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [child,initialChild,toTuple,sectorSource,sourceTuple]
  rw [source_quotient p hp x.common x.divisor hdiv]
  rfl

theorem markedModeColumn_negative_sector
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Z D B v:ℝ) :
    markedModeColumn p hp hcop hg hpr pool Ψ j (-x.frequency) x slots lists a W Z D B v=
      ∑J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        child p hp hcop hg pool Ψ j (slots\J) lists a W (Z^(columnCenter D B v))
          (negativeChild (initialChild (toTuple p (sectorSource u x)))) := by
  unfold markedModeColumn
  rw [hu]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [child,negativeChild,initialChild,toTuple,sectorSource,sourceTuple]
  rw [source_quotient p hp x.common x.divisor hdiv]
  simp only [quotient,sourcePoint,mul_neg]

end SevenEighths.InverseInitialEnergyCallerSector

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAllocation -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerAllocation
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerSector
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def modeCoefficient (Ψ:Eis→*ℂ)(j:Eis)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) : ℂ :=
  outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ *
    secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2)
      (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H)

def allocatedMode (u:Eisˣ)(pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)
    (slots J₁ J₂:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) : ℂ :=
  let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  modeCoefficient p hp hcop hg Ψ j Z D B v θ H x ρ z *
    (star (primeMark J₁ lists a (x.common∪x.overlap))*primeMark J₂ lists a (x.common∪x.overlap))*
    (star (child p hp hcop hg pool (secondRayMinus Ψ ρ) j (slots\J₁) lists a
      (childLogTest ω₁ (-height 4)) (Z^(columnCenter D B v))
      (initialChild (toTuple p (sectorSource u x))))*
      child p hp hcop hg pool (secondRayPlus Ψ ρ) j (slots\J₂) lists a
      (childLogTest ω₂ (height 5)) (Z^(columnCenter D B v))
      (negativeChild (initialChild (toTuple p (sectorSource u x)))))

theorem rowMode_eq_allocations
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) :
    rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂ Z D B v θ H x ρ z=
      ∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
  unfold rowMode
  dsimp only
  rw [markedModeColumn_sector p hp hcop hg hpr x hdiv u hu,
    markedModeColumn_negative_sector p hp hcop hg hpr x hdiv u hu]
  simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  simp only [star_mul,allocatedMode,modeCoefficient]
  ring

theorem modeCoefficient_norm_le
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (Ψ:Eis→*ℂ)(hΨ:∀n,‖Ψ n‖≤1)(j:Eis)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) :
    ‖modeCoefficient p hp hcop hg Ψ j Z D B v θ H x ρ z‖≤‖secondRayCoefficient ρ‖ := by
  simp only [modeCoefficient,norm_mul,secondOuterPhase_norm,mul_one]
  exact InverseInitialEnergyCallerWeights.outerCoefficient_norm_le p hp hcop hg hc Ψ hΨ j _ ρ

end SevenEighths.InverseInitialEnergyCallerAllocation

end

end OAI

end

