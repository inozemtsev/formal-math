module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part022
public import Green64.Library.Analysis.NumberTheory.DirichletL.IdealEuler.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part006

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part023

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.CanonicalRankDepthParameters -/

section

namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

theorem actual_rank_depth_covers (Mmax cutoff:ℝ)(hcut:0<cutoff):
    Mmax≤ rankRowCap (actualDepth Mmax (cutoff/2)) cutoff := by
  have hceil:=Nat.le_ceil (2*Mmax/(3*(cutoff/2)))
  have hscaled:2*Mmax≤(⌈2*Mmax/(3*(cutoff/2))⌉₊:ℝ)*(3*(cutoff/2)):=
    (div_le_iff₀ (by positivity:0<3*(cutoff/2))).mp hceil
  unfold rankRowCap actualDepth
  push_cast
  nlinarith

theorem actual_rank_depth_parameters (Mmax Fmax c eps:ℝ)
    (hM:0≤Mmax)(hF:0≤Fmax)(hc:0<c)(heps:0<eps):
    ∃cutoff eta:ℝ,0<cutoff ∧ 0<eta ∧ eta≤1 ∧ eta≤ cutoff/32 ∧
      cutoff≤Fmax+1 ∧ cutoff≤ c/200 ∧ eta≤ c/100000 ∧
      let n:=actualDepth Mmax (cutoff/2);
      0<n ∧ Mmax≤ rankRowCap n cutoff ∧
      ∀k:ℕ,k≤n→Fmax≤ rankTotalCap k (Fmax+1) eta ∧
        c/2≤ rankMargin k c eta ∧ rankMargin k c eta≤ c ∧
        0≤ rankLoss k eta ∧ rankLoss k eta≤eps/4 := by
  let csmall:=min c 1
  have hcs:0<csmall:=lt_min hc (by norm_num)
  have hcc:csmall≤ c:=min_le_left _ _
  have hc1:csmall≤1:=min_le_right _ _
  obtain ⟨cutoff,eta,hcut,heta,heta1,hetacut,hcutc,hetac,hbudgets⟩:=
    actual_recursion_parameters Mmax Fmax csmall eps hM hF hcs heps
  dsimp only at hbudgets
  refine ⟨cutoff,eta,hcut,heta,heta1,hetacut,by linarith,by linarith,by linarith,?_⟩
  dsimp only
  refine ⟨actualDepth_pos _ _,actual_rank_depth_covers Mmax cutoff hcut,?_⟩
  intro k hk
  have hk':(k:ℝ)≤(actualDepth Mmax (cutoff/2):ℝ):=by exact_mod_cast hk
  have hmono:=mul_le_mul_of_nonneg_right hk' heta.le
  have hk0:0≤(k:ℝ):=Nat.cast_nonneg _
  have hkE:0≤(k:ℝ)*eta:=mul_nonneg hk0 heta.le
  rcases hbudgets with ⟨hmargin,hsize,hloss⟩
  unfold rankTotalCap rankMargin rankLoss
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem actual_rank_top_parameters (Mmax Fmax c eps:ℝ)
    (hM:0≤Mmax)(hF:0≤Fmax)(hc:0<c)(heps:0<eps):
    ∃(n:ℕ)(cutoff eta:ℝ),n=actualDepth Mmax (cutoff/2) ∧
      0<n ∧ 0<cutoff ∧ 0<eta ∧ eta≤1 ∧ eta≤ cutoff/32 ∧
      cutoff≤Fmax+1 ∧ cutoff≤ c/200 ∧ eta≤ c/100000 ∧
      Mmax≤ rankRowCap n cutoff ∧ Fmax≤ rankTotalCap n (Fmax+1) eta ∧
      c/2≤ rankMargin n c eta ∧ rankMargin n c eta≤ c ∧
      0≤ rankLoss n eta ∧ rankLoss n eta<eps := by
  obtain ⟨cutoff,eta,hcut,heta,heta1,hetacut,hcutL,hcutc,hetac,hn,hrow,hall⟩:=
    actual_rank_depth_parameters Mmax Fmax c eps hM hF hc heps
  have htop:=hall (actualDepth Mmax (cutoff/2)) le_rfl
  refine ⟨actualDepth Mmax (cutoff/2),cutoff,eta,rfl,hn,hcut,heta,heta1,hetacut,
    hcutL,hcutc,hetac,hrow,htop.1,htop.2.1,htop.2.2.1,htop.2.2.2.1,?_⟩
  linarith [htop.2.2.2.2]

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CanonicalRankEnergyMonotone -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem canonical_rank_loss_le {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps eps' A:ℝ)(K degree:ℕ)
    (hZ:1≤Z)(hA:0≤A)(he:eps≤eps')
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps' A K degree :=by
  intro Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hA

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CanonicalEnergyExistenceData -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseReflectedPhase
local notation "O"=>ActualEisensteinCubic.O

def CanonicalEnergyExists (Mcap Fcap c eps L:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ)):Prop :=
  ∃degree:ℕ,∃B:ℝ,1≤B ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀D:ℕ,B*Z^L≤D→
    ∀{σ:Type}[DecidableEq σ](slots:Finset σ),slots.card≤K→
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H:σ→ℝ)(a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→
      (∀i∈slots,1≤H i)→(∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i)→
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1)→
    ∀z:ℝ,0≤z→(∏i∈slots,H i)≤Z^z→
    ∀base:O→*ℂ,(∀u,‖base u‖≤1)→
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) base→
      CompletePoolRankMoments q D slots lists a base W Z Mcap Fcap z c eps C K degree

theorem canonical_energy_of_rank (n:ℕ)(L cstar cutoff eta Mcap Fcap c eps:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ))
    (hM:Mcap≤ rankRowCap n cutoff)(hF:Fcap≤ rankTotalCap n L eta)
    (hc:rankMargin n cstar eta≤ c)(he:rankLoss n eta≤eps)
    (h:RankEnergyExists n L cstar cutoff eta K W):
    CanonicalEnergyExists Mcap Fcap c eps L K W :=by
  obtain ⟨degree,B,hB,h⟩:=h
  refine ⟨degree,B,hB,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,h⟩:=h q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  have hmom:=h Z hZ D hD slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  dsimp only [CompletePoolRankMoments] at hmom ⊢
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hFa:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  apply canonical_rank_loss_le (poolPrimary F) (poolPrimary_ne_zero F hFa) (poolPrimary_coprime F hFa)
    (poolPrimary_good F hFa) Finset.univ base slots lists a W Z Mcap Fcap z c (rankLoss n eta) eps C K degree
    (by linarith) hC.le he
  exact canonical_rank_restrict (poolPrimary F) (poolPrimary_ne_zero F hFa) (poolPrimary_coprime F hFa)
    (poolPrimary_good F hFa) Finset.univ base slots lists a W Z Mcap (rankRowCap n cutoff)
    Fcap (rankTotalCap n L eta) z c (rankMargin n cstar eta) (rankLoss n eta) C K degree hM hF hc hmom

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceSuccessor -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase InverseTerminalWidths
open CanonicalCubeSeparation CompletedHeight InverseMomentFirstSecondHeightCost
local notation "O"=>ActualEisensteinCubic.O

theorem rank_energy_exists_succ_of_reference
    (n:ℕ)(L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤ cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤ cstar/100000)(hetad:eta≤ cutoff/32)
    (hIH:∀(W:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo→0≤hi→
      Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi→RankEnergyExists n L cstar cutoff eta K W)
    (W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0→|x|≤Alog)
    (hone:∀x,|x|≤ columnWindowRadius lo hi→Vlog x=1)
    (hlarge:∀window:ℝ,∃Zt:ℝ,1<Zt ∧ ∀Z:ℝ,Zt≤Z→
      2≤Z ∧ 2≤Z^eta ∧ Real.exp 1≤Z^eta ∧ 1≤eta*Real.log Z ∧
      hi≤Z^eta ∧ Real.exp Alog≤Z^eta ∧ Real.exp window≤Z^eta):
    RankEnergyExists (n+1) L cstar cutoff eta K W :=by
  have hL0:0≤L:=by linarith
  have heF:0<firstPassEpsilon L eta:=by unfold firstPassEpsilon;positivity
  have hem:0<sourceMassEpsilon L eta:=by unfold sourceMassEpsilon;positivity
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hstep⟩:=
    actual_complete_normalized_rank_step lo hi hlo hhi W hsW (W.smooth ⊤) Vlog Alog hbox hone
      L cstar eta eta 1 (sourceMassEpsilon L eta) (sourceMassEpsilon L eta) eta
      hL hcstar heta heta1 hetac heta heta1 hem hem heta K
  obtain ⟨J11,B11,hB11,ih11⟩:=hIH w11 af1 bf1 ha1 (by linarith) (subset_closure.trans hs11)
  obtain ⟨J12,B12,hB12,ih12⟩:=hIH w12 af1 bf1 ha1 (by linarith) (subset_closure.trans hs12)
  obtain ⟨J21,B21,hB21,ih21⟩:=hIH w21 af2 bf2 ha2 (by linarith) (subset_closure.trans hs21)
  obtain ⟨J22,B22,hB22,ih22⟩:=hIH w22 af2 bf2 ha2 (by linarith) (subset_closure.trans hs22)
  let J:=J11+J12+J21+J22
  let dl:=2*(InverseClippingProfiles.momentOrder (firstDegree J)+(volume:Measure ℝ).integrablePower)
  let Jout:=max ds dl
  let B:=1+hi+B11+B12+B21+B22
  have hB:1≤B:=by dsimp [B];linarith
  have hb0:0≤B:=by linarith
  have hhiB:hi≤B:=by dsimp [B];linarith
  have hBB11:B11≤B:=by dsimp [B];linarith
  have hBB12:B12≤B:=by dsimp [B];linarith
  have hBB21:B21≤B:=by dsimp [B];linarith
  have hBB22:B22≤B:=by dsimp [B];linarith
  have hj11:J11≤J:=by dsimp [J];omega
  have hj12:J12≤J:=by dsimp [J];omega
  have hj21:J21≤J:=by dsimp [J];omega
  have hj22:J22≤J:=by dsimp [J];omega
  obtain ⟨Zt,hZt,hlarge⟩:=hlarge window
  refine ⟨Jout,B,hB,?_⟩
  intro q hq
  obtain ⟨C11,Z11,hC11,hZ11,ih11⟩:=ih11 q hq
  obtain ⟨C12,Z12,hC12,hZ12,ih12⟩:=ih12 q hq
  obtain ⟨C21,Z21,hC21,hZ21,ih21⟩:=ih21 q hq
  obtain ⟨C22,Z22,hC22,hZ22,ih22⟩:=ih22 q hq
  obtain ⟨Cs,Cb,Zs,hCs,hCb,hZs,hstep⟩:=hstep (firstPassEpsilon L eta) eta heF heta J q hq
  let A:=C11+C12+C21+C22
  have hA:0≤A:=by dsimp [A];linarith
  have hCA11:C11≤A:=by dsimp [A];linarith
  have hCA12:C12≤A:=by dsimp [A];linarith
  have hCA21:C21≤A:=by dsimp [A];linarith
  have hCA22:C22≤A:=by dsimp [A];linarith
  let C:=(Cs+Cb)*(1+A)
  let Z₀:=Zs+Zt+Z11+Z12+Z21+Z22
  have hC:0<C:=by dsimp [C];positivity
  have hZ₀:1<Z₀:=by dsimp [Z₀];linarith
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have hZs':Zs≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZt':Zt≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ11':Z11≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ12':Z12≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ21':Z21≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ22':Z22≤Z:=by dsimp [Z₀] at hZ;linarith
  obtain ⟨hZ2,h2,hExp,hlog,hhiZ,hAZ,hwin⟩:=hlarge Z hZt'
  have hZ1:1<Z:=by linarith
  have hZ0:0<Z:=by linarith
  have hD11:B11*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB11 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD12:B12*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB12 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD21:B21*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB21 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD22:B22*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB22 (Real.rpow_nonneg hZ0.le _)).trans hD
  have m11:=ih11 Z hZ11' D hD11 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m12:=ih12 Z hZ12' D hD12 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m21:=ih21 Z hZ21' D hD21 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m22:=ih22 Z hZ22' D hD22 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only [CompletePoolRankMoments] at m11 m12 m21 m22 ⊢
  intro Ψ hΨ m hm N V M Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels theta
  have hcap:N+V≤L:=by
    unfold rankTotalCap at hFc
    have hh:0≤15*((n+1:ℕ):ℝ)*eta:=by positivity
    linarith
  have hcm:0≤ rankMargin (n+1) cstar eta:=by unfold rankMargin;positivity
  obtain ⟨hNL,hVL,hMF,hQL,hzL,hwidth,hmargin',hmL,hpuncture⟩:=
    actual_rank_state_gates m hm Z N V M Qwidth z (rankMargin (n+1) cstar eta) L
      hZ1 hN hV hM hQ hz hcm hcap hmargin hnorm
  obtain ⟨hΨnorm,hΨperiod⟩:=actual_rank_family_gates q base hbase hperiod Ψ hΨ
  have hDparent:hi*Z^N≤D:=by
    calc
      _≤B*Z^L:=mul_le_mul hhiB (Real.rpow_le_rpow_of_exponent_le hZ1.le hNL)
        (Real.rpow_nonneg hZ0.le _) hb0
      _≤D:=hD
  have hsscard:ss.card≤K:=(Finset.card_le_card hss).trans hslots
  have hssdis:(ss:Set σ).PairwiseDisjoint lists:=by
    intro i hi j hj hij
    exact hdis (hss hi) (hss hj) hij
  have hssH:∀i∈ss,1≤H i:=fun i hi=>hH i (hss hi)
  have hssP:∀i∈ss,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i:=fun i hi=>hP i (hss hi)
  have hssa:∀i∈ss,∀P∈lists i,‖a i P‖≤1:=fun i hi=>ha i (hss hi)
  have hssprod:(∏i∈ss,H i)≤Z^z:=canonical_rank_subslot_cap slots ss H Z z hss hH hprod
  obtain ⟨hsmallM,hsmallF,hsmallc⟩:=actual_rank_successor_caps n L cstar cutoff eta M (N+V)
    (rankMargin (n+1) cstar eta) hMc hFc le_rfl
  have lift (w:𝓢(ℝ,ℂ))(Cw:ℝ)(Jw:ℕ)(hCw:0≤Cw)(hCwA:Cw≤A)(hJw:Jw≤J)
      (mw:CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a w Z (rankRowCap n cutoff)
        (rankTotalCap n L eta) z (rankMargin n cstar eta) (rankLoss n eta) Cw K Jw):
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base ss lists a w Z (M-3*(cutoff/2)/2)
        (N+V+15*eta) z (rankMargin (n+1) cstar eta-7*eta) (rankLoss n eta) A K J:=by
    apply canonical_rank_subslots (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots ss lists a w Z _ _ z _ _ A K J hss
    apply canonical_rank_restrict (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a w Z
      (M-3*(cutoff/2)/2) (rankRowCap n cutoff) (N+V+15*eta) (rankTotalCap n L eta)
      z (rankMargin (n+1) cstar eta-7*eta) (rankMargin n cstar eta) (rankLoss n eta) A K J
      (by linarith) hsmallF hsmallc
    exact canonical_rank_height_constant (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a w Z _ _ z _ _ Cw A K Jw J
      hZ0 hCw hCwA hJw mw
  have hechild:0≤ rankLoss n eta:=by unfold rankLoss;positivity
  obtain ⟨_,_,hpieta,hmass,hret,hprincipal0,hcost⟩:=actual_step_parameters L eta 0 0 (rankLoss n eta)
    hL0 heta heta1 (by linarith) (by linarith) hechild
  obtain ⟨hprincipal,hFirst,hFinal⟩:=actual_complete_step_cost L eta (rankLoss n eta) hL0 heta heta1 hechild
  have hreserve:cstar/2≤ rankMargin (n+1) cstar eta:=by
    unfold rankMargin
    exact le_add_of_nonneg_right (by positivity)
  have hbound:=hstep m hm Z N V M z (rankMargin (n+1) cstar eta) cutoff (8*eta)
    (rankLoss n eta) A (rankLoss n eta+58*eta) (rankLoss n eta+60*eta) theta
    hZs' hZ2 h2 hExp hlog hN hV hM hcap hMF hzL hhiZ hAZ hwin hcut hcutL hcutc hetad hmL hmargin'
    hreserve (by simpa only [hwidth] using hpuncture) (by positivity) hpieta hmass hmass hechild
    (by linarith) hret hprincipal hcost (by linarith) hA
    labels (fun I hI=>⟨⟨(hlabels I hI).1.1,(hlabels I hI).1.2.2⟩,(hlabels I hI).1.2.1,(hlabels I hI).2⟩)
    D hDparent ss hsscard lists H hssdis hssH hssP hssprod base Ψ hΨ hΨnorm hΨperiod a hssa
    (lift w11 C11 J11 hC11.le hCA11 hj11 m11) (lift w12 C12 J12 hC12.le hCA12 hj12 m12)
    (lift w21 C21 J21 hC21.le hCA21 hj21 m21) (lift w22 C22 J22 hC22.le hCA22 hj22 m22)
  have hnextLoss:rankLoss n eta+62*eta=rankLoss (n+1) eta:=by unfold rankLoss;push_cast;ring
  have hlongexp:(rankLoss n eta+60*eta)+2*L*firstPassEpsilon L eta+eta≤ rankLoss (n+1) eta:=by
    simpa only [hnextLoss] using hFinal
  have hloss0:0≤ rankLoss (n+1) eta:=by unfold rankLoss;positivity
  have hlong:Cb*(1+A)*(1+‖theta‖)^dl*
      Z^(N+V+(rankLoss n eta+60*eta)+2*L*firstPassEpsilon L eta+eta)≤
      Cb*(1+A)*(1+‖theta‖)^dl*Z^(N+V+rankLoss (n+1) eta):=by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hZ1.le
    linarith
  have hh:=hbound.trans (add_le_add le_rfl hlong)
  have hmrg:=actual_complete_height_merge ds dl Z (N+V) cstar (rankLoss (n+1) eta) Cs Cb A theta
    hZ1.le hcstar.le hloss0 hCs.le hCb hA
  have hpow:(1+‖theta‖)^Jout≤(1+‖theta‖)^(2*Jout):=
    pow_le_pow_right₀ (by linarith [norm_nonneg theta]) (by omega)
  have hf:childLogTest W theta=normTwistedSource W theta:=by
    funext y
    simp only [childLogTest,normTwistedSource,mul_comm]
  rw [hf]
  apply (hh.trans hmrg).trans
  dsimp only [C,Jout]
  have hx:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (show 0≤(Cs+Cb)*(1+A) by positivity))
    (Real.rpow_nonneg hZ0.le (N+V+rankLoss (n+1) eta))
  convert hx using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceInduction -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open CanonicalCubeSeparation

def RankReferenceCutoffs:Prop :=
  ∀lo hi:ℝ,0<lo→0≤hi→∃(Vlog:𝓢(ℝ,ℂ))(Alog:ℝ),
    (∀x,Vlog x≠0→|x|≤Alog) ∧
    (∀x,|x|≤ columnWindowRadius lo hi→Vlog x=1)

def RankReferenceThresholds:Prop :=
  ∀eta:ℝ,0<eta→∀hi Alog window:ℝ,∃Zt:ℝ,1<Zt ∧ ∀Z:ℝ,Zt≤Z→
    2≤Z ∧ 2≤Z^eta ∧ Real.exp 1≤Z^eta ∧ 1≤eta*Real.log Z ∧
    hi≤Z^eta ∧ Real.exp Alog≤Z^eta ∧ Real.exp window≤Z^eta

theorem rank_energy_exists_all_of_references
    (href:RankReferenceCutoffs)(hthreshold:RankReferenceThresholds)
    (L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤ cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤ cstar/100000)(hetad:eta≤ cutoff/32):
    ∀n:ℕ,∀(W:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo→0≤hi→
      Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi→RankEnergyExists n L cstar cutoff eta K W :=by
  intro n
  induction n with
  | zero =>
      intro W lo hi hlo hhi hsW
      exact rank_energy_exists_zero L cstar cutoff eta hcut K W
  | succ n ih =>
      intro W lo hi hlo hhi hsW
      obtain ⟨Vlog,Alog,hbox,hone⟩:=href lo hi hlo hhi
      exact rank_energy_exists_succ_of_reference n L cstar cutoff eta K hL hcstar hcut hcutL
        hcutc heta heta1 hetac hetad ih W lo hi hlo hhi hsW Vlog Alog hbox hone
        (fun window=>hthreshold eta heta hi Alog window)

theorem canonical_energy_exists_of_references
    (href:RankReferenceCutoffs)(hthreshold:RankReferenceThresholds)
    (Mcap Fcap c eps:ℝ)(hM:0≤Mcap)(hF:0≤Fcap)(hc:0<c)(heps:0<eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    CanonicalEnergyExists Mcap Fcap c eps (Fcap+1) K W :=by
  obtain ⟨n,cutoff,eta,hn,hpos,hcut,heta,heta1,hetad,hcutL,hcutc,hetac,hrow,hcap,hmargin0,hmargin,hloss0,hloss⟩:=
    actual_rank_top_parameters Mcap Fcap c eps hM hF hc heps
  have he:=rank_energy_exists_all_of_references href hthreshold (Fcap+1) c cutoff eta K
    (by linarith) hc hcut hcutL hcutc heta heta1 hetac hetad n W lo hi hlo hhi hsW
  exact canonical_energy_of_rank n (Fcap+1) c cutoff eta Mcap Fcap c eps K W
    hrow hcap hmargin hloss.le he

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistence -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment

theorem actual_rank_reference_cutoffs : RankReferenceCutoffs :=by
  intro lo hi hlo hhi
  obtain ⟨Vlog,Alog,hA,hAe,hcompact,hsupport,hbox,hone,hzero⟩:=
    exists_canonical_reference_cutoff lo hi
  exact ⟨Vlog,Alog,hbox,hone⟩

theorem actual_rank_reference_thresholds : RankReferenceThresholds :=by
  intro eta heta hi Alog window
  exact eventually_canonical_reference_gates hi Alog window eta heta

theorem canonical_rank_energy_exists
    (L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤ cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤ cstar/100000)(hetad:eta≤ cutoff/32)
    (n:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    RankEnergyExists n L cstar cutoff eta K W :=
  rank_energy_exists_all_of_references actual_rank_reference_cutoffs actual_rank_reference_thresholds
    L cstar cutoff eta K hL hcstar hcut hcutL hcutc heta heta1 hetac hetad n W lo hi hlo hhi hsW

theorem canonical_marked_energy_exists
    (Mcap Fcap c eps:ℝ)(hM:0≤Mcap)(hF:0≤Fcap)(hc:0<c)(heps:0<eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    CanonicalEnergyExists Mcap Fcap c eps (Fcap+1) K W :=
  canonical_energy_exists_of_references actual_rank_reference_cutoffs actual_rank_reference_thresholds
    Mcap Fcap c eps hM hF hc heps K W lo hi hlo hhi hsW

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalEnergy -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialCanonicalEnergy
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CanonicalQuadraticSieve
open InverseMoment InverseInitialClippedColumns SecondPassArithmetic CanonicalCoefficientClass
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq σ] in
theorem normalization_change (pool:Finset ι)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(w:Ideal O→ℝ)(W:ℝ→ℂ)
    (X Z F G:ℝ)(hZ:0<Z):
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z F=
      Z^(G-F)*normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z G := by
  have he:Z^F*normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z F=
      Z^G*normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z G:=
    (columnEnergy_normalization p hp hcop hg pool Ψ m slots lists a labels rows w W X hZ F).symm.trans
      (columnEnergy_normalization p hp hcop hg pool Ψ m slots lists a labels rows w W X hZ G)
  apply mul_left_cancel₀ (Real.rpow_pos_of_pos hZ F).ne'
  rw [←mul_assoc,←Real.rpow_add hZ,show F+(G-F)=G by ring]
  exact he

omit [DecidableEq σ] in
theorem energy_range_weight_le (pool:Finset ι)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows largeRows:Finset O)(w v:Ideal O→ℝ)(W:ℝ→ℂ)
    (X Z F:ℝ)(hrows:rows⊆largeRows)(hw:∀f∈labels,0≤w f)(hv:∀f∈labels,w f≤v f):
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z F≤
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels largeRows v W X Z F := by
  unfold normalizedColumnEnergy
  apply Finset.sum_le_sum
  intro f hf
  apply mul_le_mul (hv f hf)
    (Finset.sum_le_sum_of_subset_of_nonneg hrows (fun _ _ _=>sq_nonneg _))
    (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
    ((hw f hf).trans (hv f hf))

omit [DecidableEq σ] in
theorem initial_child_from_rank (pool:Finset ι)(base Ψ:O→*ℂ)
    (slots subslots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:𝓢(ℝ,ℂ))
    (Z Mcap Fcap z c eps A N V M Q η:ℝ)(K degree:ℕ)(m:O)
    (hZ:1<Z)(hbase:IsBaseRayTwist base Ψ)(hm:m≠0)
    (hN:0≤N)(hV:0≤V+2*η)(hM:0≤M)(hQ:0≤Q)
    (hMcap:M≤Mcap)(hFcap:N+(V+2*η)≤Fcap)
    (hmargin:CanonicalMargins (N+(V+2*η)) M Q z c)
    (hmnorm:‖eisEmbedding m‖^2=Z^Q)(hsub:subslots⊆slots)
    (labels:Finset (Ideal O))(hlabels:∀f∈labels,Admissible f ∧ (f.absNorm:ℝ)≤Z^(V+2*η))
    (rows:Finset O)(hrows:rows⊆nonzeroChildFrequencyBall 1 (Z^M))
    (weight:Ideal O→ℝ)(hw:∀f∈labels,0≤weight f)
    (hweight:∀f∈labels,weight f≤ secondLabelWeight K f)(s:ℝ)
    (hmoment:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z Mcap Fcap z c eps A K degree):
    normalizedColumnEnergy p hp hcop hg pool Ψ m subslots lists a labels rows weight
      (childLogTest W s) (Z^N) Z (N+V)≤A*Z^(N+V+eps+4*η)*(1+‖s‖)^(2*degree) := by
  have hcanon:=hmoment Ψ hbase m hm N (V+2*η) M Q hN hV hM hQ hMcap hFcap hmargin hmnorm
    subslots hsub labels hlabels s
  rw [normalization_change p hp hcop hg pool Ψ m subslots lists a labels rows weight
    (childLogTest W s) (Z^N) Z (N+V) (N+(V+2*η)) (zero_lt_one.trans hZ)]
  apply (mul_le_mul_of_nonneg_left
    ((energy_range_weight_le p hp hcop hg pool Ψ m subslots lists a labels rows
      (nonzeroChildFrequencyBall 1 (Z^M)) weight (secondLabelWeight K) (childLogTest W s)
      (Z^N) Z (N+(V+2*η)) hrows hw hweight).trans hcanon)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans_eq
  rw [show N+(V+2*η)-(N+V)=2*η by ring]
  calc
    _=A*(Z^(2*η)*Z^(N+(V+2*η)+eps))*(1+‖s‖)^(2*degree):=by ring
    _=_:=by
      rw [←Real.rpow_add (zero_lt_one.trans hZ)]
      congr 3
      ring

end SevenEighths.InverseInitialCanonicalEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerUniform -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic CompletedGauss
namespace SevenEighths.InverseInitialEnergyCallerUniform
open InverseMoment InverseInitialClippedColumns InverseInitialProfile
local notation "Eis"=>ActualEisensteinCubic.O

theorem initial_height_bound (J:ℕ)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
    (h:ℝ)(hh:h = -leftHeight z ∨ h=rightHeight z) :
    (1+‖h‖)^(2*J)≤tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2 := by
  have hb := child_height_moment_bound (2*J) z
  have hl : 1≤(1+‖leftHeight z‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg (leftHeight z)])
  have hr : 1≤(1+‖rightHeight z‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg (rightHeight z)])
  rw [show 2*(2*J)=4*J by omega] at hb
  rcases hh with rfl|rfl
  · rw [norm_neg]
    exact (le_mul_of_one_le_right (by positivity) hr).trans hb
  · exact (le_mul_of_one_le_left (by positivity) hl).trans hb

theorem initial_raw_uniform
    (W:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hs:Function.support W⊆Set.Icc lo b)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(m:Eis)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)(D:Ideal Eis→ℝ)(_hD:∀f∈labels,0≤D f)
      (Z N F E:ℝ)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))(h:ℝ),1<Z→0≤E→
      (h = -leftHeight z ∨ h=rightHeight z)→
      (∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) (Z^(max 0 N)) Z F≤E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest W h) (Z^N) Z F≤C*E*(tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) := by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,huniform⟩ := canonical_clipped_uniform W lo b b hlo hb hs hW
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  obtain ⟨C,hC,hbound⟩ := huniform J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD Z N F E z h hZ hE hh hm
  by_cases hne:(freshColumns p pool W (Z^N)).Nonempty
  · obtain ⟨hc1,hcb⟩ := freshColumns_clipping_range p hp pool W lo b Z N hZ hb hs hne
    rw [InverseInitialEnergyCallerClipping.normalized_energy_clipping p hp hcop hg
      pool Ψ m slots lists a labels rows D W (by linarith) N h F]
    apply (hbound p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
      (Z^(max 0 N-N)) h (Z^(max 0 N)) Z F E hc1 hcb (by positivity) hE hm).trans
    exact mul_le_mul_of_nonneg_left (initial_height_bound J z h hh) (mul_nonneg hC.le hE)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    unfold normalizedColumnEnergy
    simp_rw [canonical_row_zero_of_freshColumns_empty p hp hcop hg pool Ψ m _ _
      slots lists a W (Z^N) h he,mul_zero,norm_zero,zero_pow (by omega : (2:ℕ)≠0),
      Finset.sum_const_zero,mul_zero,Finset.sum_const_zero]
    dsimp [tripleHeight,coordinateHeight]
    positivity

end SevenEighths.InverseInitialEnergyCallerUniform

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerReference -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerReference
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerBranch
local notation "Eis"=>ActualEisensteinCubic.O
local instance initialEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem actual_physical_reference_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(V:Fin 6→ℝ→ℂ)(M:Fin 6→ℝ)
    (hV:∀i,ContDiff ℝ ∞ (V i))(hS:∀i,HasCompactSupport (V i))
    (hM:∀i,0≤M i)(hbox:∀i y,V i y≠0→|y|≤M i)
    (ω₁ ω₂:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hω₁:Function.support ω₁⊆Set.Icc lo b)(hω₂:Function.support ω₂⊆Set.Icc lo b)
    (hd₁:ContDiff ℝ ∞ ω₁)(hd₂:ContDiff ℝ ∞ ω₂) :
    ∃(fresh₁ fresh₂:𝓢(ℝ,ℂ)),
      (∃af bf:ℝ,0<af ∧ af≤bf ∧ HasCompactSupport (fresh₁:ℝ→ℂ) ∧
        tsupport (fresh₁:ℝ→ℂ)⊆Set.Icc af bf) ∧
      (∃af bf:ℝ,0<af ∧ af≤bf ∧ HasCompactSupport (fresh₂:ℝ→ℂ) ∧
        tsupport (fresh₂:ℝ→ℂ)⊆Set.Icc af bf) ∧
    ∀(J N:ℕ)(U π:ℝ),0≤U→0<π→∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (Z D B v θ H R m η:ℝ)(_hZ:1<Z)(_hR:R≤U)
      (_hη:0≤η*Real.log Z)(c₁ c₂ θ₁ θ₂:ℝ)(_hc₁:0<c₁)(_hc₂:0<c₂)
      (_hsupport:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A ε:ℝ)(_hA:0≤A)
      (_hδ:max 0 (columnCenter D B v)-columnCenter D B v≤3*η)
      (_hF:F=D-B+θ+(max 0 (columnCenter D B v)-columnCenter D B v))
      (_hReq:R=B-θ+2*η)
      (_hmoment:∀s:ℝ,∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest fresh₁ s)
          (Z^(max 0 (columnCenter D B v))) Z F≤(A*Z^(F+ε))*(1+‖s‖)^(2*J) ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest fresh₂ s)
          (Z^(max 0 (columnCenter D B v))) Z F≤(A*Z^(F+ε))*(1+‖s‖)^(2*J)),
      ‖physicalBlock p hp hcop hg (pointSource pool S) (w ∘ erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+11*η+π+ε)*A*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)) := by
  obtain ⟨fresh₁,af₁,bf₁,haf₁,hab₁,hc₁,hsf₁,hu₁⟩ :=
    InverseInitialEnergyCallerUniform.initial_raw_uniform ω₁ lo b hlo hb hω₁ hd₁
  obtain ⟨fresh₂,af₂,bf₂,haf₂,hab₂,hc₂,hsf₂,hu₂⟩ :=
    InverseInitialEnergyCallerUniform.initial_raw_uniform ω₂ lo b hlo hb hω₂ hd₂
  refine ⟨fresh₁,fresh₂,⟨af₁,bf₁,haf₁,hab₁,hc₁,hsf₁⟩,⟨af₂,bf₂,haf₂,hab₂,hc₂,hsf₂⟩,?_⟩
  intro J N U π hU hπ
  obtain ⟨C₁,hC₁,hh₁⟩ := hu₁ J
  obtain ⟨C₂,hC₂,hh₂⟩ := hu₂ J
  obtain ⟨Cp,hCp,hphysical⟩ := InverseInitialEnergyCallerPhysical.actual_physical_block_bound
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox (4*J) N U π hU hπ
  refine ⟨Cp*(C₁+C₂),mul_pos hCp (add_pos hC₁ hC₂),?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha
    Z D B v θ H R m η hZ hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F A ε hA hδ hF hReq hmoment
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hm : ∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,
      ∀J₁∈slots.powerset,∀J₂∈slots.powerset,∀t∈quotientSet p S,
      normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
        (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
        (Z^(columnCenter D B v)) Z F≤((C₁+C₂)*(A*Z^(F+ε)))*
          (tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) ∧
      normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
        (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
        (Z^(columnCenter D B v)) Z F≤((C₁+C₂)*(A*Z^(F+ε)))*
          (tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) := by
    intro z ρ J₁ hJ₁ J₂ hJ₂ t ht
    have hb₁ := hh₁ p hp hcop hg hpr pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
      (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
      (by intros;positivity) Z (columnCenter D B v) F (A*Z^(F+ε)) z (-leftHeight z)
      hZ (by positivity) (Or.inl rfl) (fun s=>(hmoment s ρ J₁ hJ₁ J₂ hJ₂ t ht).1)
    have hb₂ := hh₂ p hp hcop hg hpr pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
      (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
      (by intros;positivity) Z (columnCenter D B v) F (A*Z^(F+ε)) z (rightHeight z)
      hZ (by positivity) (Or.inr rfl) (fun s=>(hmoment s ρ J₁ hJ₁ J₂ hJ₂ t ht).2)
    rw [leftHeight_eq] at hb₁
    rw [rightHeight_eq] at hb₂
    have hh : 0≤tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2 := by
      dsimp [tripleHeight,coordinateHeight];positivity
    constructor
    · apply hb₁.trans
      gcongr
      linarith
    · apply hb₂.trans
      gcongr
      linarith
  have hb := hphysical p hp hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha
    ω₁ ω₂ Z D B v θ H R m η hZ.le hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F ((C₁+C₂)*(A*Z^(F+ε))) (by positivity) hm
  apply hb.trans
  have he : prefactorCenter m D B θ+3*η+F+R+π+(F+ε)≤ m+11*η+π+ε := by
    rw [hF,hReq]
    exact InverseInitialEnergyCallerClipping.initial_scalar_le m D B v θ η _ π ε hδ
  have hexp := Real.rpow_add hZp (prefactorCenter m D B θ+3*η+F+R+π) (F+ε)
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le he
  calc
    _=(Cp*(C₁+C₂))*Z^(prefactorCenter m D B θ+3*η+F+R+π+(F+ε))*A*
        ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)) := by rw [hexp];ring
    _≤_ := by gcongr

end SevenEighths.InverseInitialEnergyCallerReference

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerGeometry -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerGeometry
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialProfile InverseInitialClippedColumns ConcreteTraceCRT
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem outerCoefficient_nonzero_coprime
    (Ψ:Eis→*ℂ)(j:Eis)(x:Point ι)(ρ:SecondRayIndex)
    (hn:outerCoefficient p hp hcop hg Ψ j x ρ≠0) :
    IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common) := by
  apply sourceIdeal_coprime_of_not_mem p
  intro i hi hc
  have hmc : j*(∏k∈x.common,p k)∈Ideal.span {p i} := Ideal.mul_mem_left _ j hc
  have hz : rowCoprimeMask (fun i=>Ideal.span {p i}) x.overlap (j*(∏k∈x.common,p k))=0 := by
    simp only [rowCoprimeMask,ite_eq_left (show ∃i∈x.overlap,j*(∏k∈x.common,p k)∈Ideal.span {p i}
      from ⟨i,hi,hmc⟩)]
  apply hn
  simp only [outerCoefficient,initialColumn,hz,mul_zero,zero_mul,star_zero]

theorem original_nonzero_child_squarefree
    (Ψ:Eis→*ℂ)(j:Eis)(x:Source (ι:=ι) 0)(ρ:SecondRayIndex)
    (hd:x.divisor⊆x.common)
    (hn:outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ≠0)(u:Eisˣ) :
    Squarefree (initialChild (toTuple p (sectorSource u x))).2.1 := by
  change Squarefree (sourceIdeal p x.divisor*sourceIdeal p x.overlap)
  have hc := outerCoefficient_nonzero_coprime p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ hn
  change IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common) at hc
  have hdv := sourceIdeal_dvd p x.divisor x.common hd
  have hcd : IsCoprime (sourceIdeal p x.divisor) (sourceIdeal p x.overlap) :=
    hc.symm.of_isCoprime_of_dvd_left hdv
  exact squarefree_mul_iff.mpr ⟨hcd.isRelPrime,sourceIdeal_squarefree p hcop x.divisor,
    sourceIdeal_squarefree p hcop x.overlap⟩

omit [DecidableEq ι] in
theorem initial_child_label_norm (x:Source (ι:=ι) 0)(u:Eisˣ) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)=
      (sourceIdeal p x.divisor).absNorm*(sourceIdeal p x.overlap).absNorm := by
  change ((sourceIdeal p x.divisor*sourceIdeal p x.overlap).absNorm:ℝ)=_
  simp only [map_mul,Nat.cast_mul]

include hp in

theorem initial_child_row_norm (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ) :
    ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2=
      ((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2 := by
  change ‖eisEmbedding (primaryGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency))‖^2=_
  have he : primaryGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency)=
      ((u^5:Eisˣ):Eis)*(primaryGenerator (sourceIdeal p x.divisor)*x.frequency) := by
    change primaryGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency)=
      (u:Eis)^5*(primaryGenerator (sourceIdeal p x.divisor)*x.frequency)
    ring
  rw [he,GaussGeneratorTransport.norm_eisEmbedding_unit_mul,map_mul,norm_mul,mul_pow]
  rw [eisEmbedding_norm_sq_eq_absNorm_span,sourceIdeal_gen p hp hpr]
  rfl

include hp in
theorem initial_child_row_ball (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ)(R:ℝ) :
    (initialChild (toTuple p (sectorSource u x))).2.2∈nonzeroChildFrequencyBall 1 R ↔
    0<((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2 ∧
      ((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2≤R := by
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul,initial_child_row_norm p hp hpr]

include hp in

theorem initial_child_enclosures
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ)(Z θ v H η:ℝ)(hZ:0<Z)
    (hd:((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η))
    (hh:‖eisEmbedding x.frequency‖^2≤Z^(H+η)) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)≤Z^(θ+v+2*η) ∧
      ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2≤Z^(θ+H+2*η) := by
  rw [initial_child_label_norm p,initial_child_row_norm p hp hpr]
  constructor
  · apply (mul_le_mul hd hv (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  · apply (mul_le_mul hd hh (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring

end SevenEighths.InverseInitialEnergyCallerGeometry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSourceMask -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerSourceMask
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialProfile ConcreteTraceCRT
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def coprimeSource (S:Finset (Source (ι:=ι) 0)) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common))

theorem physicalBlock_coprimeSource
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(H:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j H W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (coprimeSource p S)) (w∘erasePoint)
      Ψ j H W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,coprimeSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hc:IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common)
  · rw [ite_eq_left hc]
  · rw [ite_eq_right hc]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro M hM
    apply Finset.sum_eq_zero
    intro ρ hρ
    have hxpoint : sourcePoint x N M∈pointSource pool S := by
      apply Finset.mem_biUnion.mpr
      refine ⟨x,hx,?_⟩
      apply Finset.mem_image.mpr
      exact ⟨(N,M),Finset.mem_product.mpr ⟨hN,hM⟩,rfl⟩
    have hv := pointSource_valid pool S hdiv hf _ hxpoint
    rw [physicalTerm_extracted p hp hcop hg hpr Ψ j H W₁ W₂ Φ Z D m _ hv ρ]
    have hz : outerCoefficient p hp hcop hg Ψ j (sourcePoint x N M) ρ=0 := by
      by_contra hn
      exact hc (outerCoefficient_nonzero_coprime p hp hcop hg Ψ j (sourcePoint x N M) ρ hn)
    simp only [hz,zero_mul,mul_zero]

include hcop in
theorem retained_child_squarefree
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    Squarefree (initialChild (toTuple p (sectorSource u x))).2.1 := by
  obtain ⟨hxs,hcoprime⟩ := Finset.mem_filter.mp hx
  change Squarefree (sourceIdeal p x.divisor*sourceIdeal p x.overlap)
  have hc := hcoprime.symm.of_isCoprime_of_dvd_left (sourceIdeal_dvd p _ _ (hdiv x hxs))
  exact squarefree_mul_iff.mpr ⟨hc.isRelPrime,sourceIdeal_squarefree p hcop _,
    sourceIdeal_squarefree p hcop _⟩

def childLabels (S:Finset (Source (ι:=ι) 0)) : Finset (Ideal Eis) :=
  (coprimeSource p S).image (fun x=>sourceIdeal p x.divisor*sourceIdeal p x.overlap)

include hp in
omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
theorem childLabels_ne_zero (S:Finset (Source (ι:=ι) 0)) :
    ∀f∈childLabels p S,f≠0 := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  exact mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)

include hcop in
theorem childLabels_squarefree (S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common) : ∀f∈childLabels p S,Squarefree f := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  exact retained_child_squarefree p hcop S hdiv hx 1

omit [DecidableEq ι] in
theorem child_label_mem (S:Finset (Source (ι:=ι) 0))
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    (initialChild (toTuple p (sectorSource u x))).2.1∈childLabels p S :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem nonzero_child_ball_neg (R:ℝ)(k:Eis)(hk:k∈nonzeroChildFrequencyBall 1 R) :
    -k∈nonzeroChildFrequencyBall 1 R := by
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul] at hk ⊢
  simpa only [map_neg,norm_neg] using hk

end SevenEighths.InverseInitialEnergyCallerSourceMask

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerRanges -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerRanges
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialEnergyCallerSourceMask
open InverseInitialProfile ConcreteTraceCRT CanonicalQuadraticSieve
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp hcop hg

omit [DecidableEq ι] in
theorem sourceIdeal_admissible (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset ι) : Admissible (sourceIdeal p S) := by
  refine ⟨sourceIdeal_ne_zero p hp S,sourceIdeal_squarefree p hcop S,?_⟩
  intro P hP
  obtain ⟨hprime,hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff
    (sourceIdeal_ne_zero p hp S)).mp hP
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod] at hdiv
  obtain ⟨i,hi,hPi⟩ := (hprime.dvd_finsetProd_iff (fun i=>Ideal.span {p i})).mp hdiv
  have he := (prime_dvd_prime_iff_eq hprime (sourcePrime p i).property).mp hPi
  rw [he]
  exact ⟨hg i,hc i⟩

theorem retained_label_admissible (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    Admissible (initialChild (toTuple p (sectorSource u x))).2.1 := by
  have hs := (supported_mul_iff (sourceIdeal p x.divisor) (sourceIdeal p x.overlap)).mpr
    ⟨admissible_supported (sourceIdeal_admissible p hp hcop hg hc _),
      admissible_supported (sourceIdeal_admissible p hp hcop hg hc _)⟩
  exact ⟨hs.1,retained_child_squarefree p hcop S hdiv hx u,hs.2⟩

theorem childLabels_subset_range
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (Z θ v η:ℝ)(hZ:0<Z)
    (hd:∀x∈coprimeSource p S,((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:∀x∈coprimeSource p S,((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η)) :
    childLabels p S⊆idealRange (Z^(θ+v+2*η)) := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  apply mem_idealRange.mpr
  refine ⟨retained_label_admissible p hp hcop hg hc S hdiv hx 1,?_⟩
  change ((sourceIdeal p x.divisor*sourceIdeal p x.overlap).absNorm:ℝ)≤_
  rw [map_mul,Nat.cast_mul]
  apply (mul_le_mul (hd x hx) (hv x hx) (by positivity) (by positivity)).trans_eq
  rw [←Real.rpow_add hZ]
  congr 1
  ring

theorem canonical_child_domains
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (hf:∀x∈S,x.frequency≠0)(Z θ v H η:ℝ)(hZ:0<Z)
    (hd:∀x∈coprimeSource p S,((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:∀x∈coprimeSource p S,((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η))
    (hh:∀x∈coprimeSource p S,‖eisEmbedding x.frequency‖^2≤Z^(H+η)) :
    ∀x∈coprimeSource p S,∀u:Eisˣ,
      (initialChild (toTuple p (sectorSource u x))).2.1∈idealRange (Z^(θ+v+2*η)) ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈
        nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)) := by
  intro x hx u
  refine ⟨childLabels_subset_range p hp hcop hg hc hpr S hdiv Z θ v η hZ hd hv
    (child_label_mem p S hx u),?_⟩
  rw [initial_child_row_ball p hp hpr]
  refine ⟨mul_pos ?_ (sq_pos_of_pos (norm_pos_iff.mpr
    (eisEmbedding_ne_zero (hf x (Finset.mem_filter.mp hx).1)))),?_⟩
  · exact_mod_cast Nat.pos_of_ne_zero (fun h=>sourceIdeal_ne_zero p hp x.divisor
      (Ideal.absNorm_eq_zero_iff.mp h))
  · have he := (initial_child_enclosures p hp hpr x u Z θ v H η hZ
      (hd x hx) (hv x hx) (hh x hx)).2
    rwa [initial_child_row_norm p hp hpr] at he

end SevenEighths.InverseInitialEnergyCallerRanges

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindows -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerWindows
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialEnergyCallerSourceMask
open InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def sourceRelative (x:Source (ι:=ι) 0)(Z D B v θ H:ℝ) : Fin 6→ℝ :=
  relativeNorm (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H

def windowSource (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)
    (Z D B v θ H:ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>outerCutoff ψ (sourceRelative p x Z D B v θ H)≠0)

omit [DecidableEq ι] in
theorem sourceRelative_four (x:Source (ι:=ι) 0)(N M:Finset ι)
    (Z D B v θ H:ℝ)(i:Fin 4) :
    relativeNorm (coordinates p (sourcePoint x N M)) Z D B v θ H (InverseSecondChildWindows.outerIndex i)=
      sourceRelative p x Z D B v θ H (InverseSecondChildWindows.outerIndex i) := by
  fin_cases i <;> simp only [InverseSecondChildWindows.outerIndex,sourceRelative,relativeNorm,
    coordinates,sourcePoint,physicalCoordinates,secondRelativeNorm,Fin.castLE,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Matrix.cons_val_zero',Matrix.cons_val_succ']

theorem windowSource_four_nonzero
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ)
    {x:Point ι}(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H))(i:Fin 4) :
    ψ i (relativeNorm (coordinates p x) Z D B v θ H (InverseSecondChildWindows.outerIndex i))≠0 := by
  obtain ⟨s,hs,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  have ho := (Finset.mem_filter.mp hs).2
  change outerCutoff ψ (sourceRelative p s Z D B v θ H)≠0 at ho
  rw [sourceRelative_four]
  have h := mul_ne_zero_iff.mp ho
  have h' := mul_ne_zero_iff.mp h.1
  have h'' := mul_ne_zero_iff.mp h'.1
  fin_cases i
  · exact h''.1
  · exact h''.2
  · exact h'.2
  · exact h.2

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_windowSource
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)
    (Z D B v θ H m:ℝ)(w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ)) :
    physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*outerCutoff ψ (sourceRelative p x Z D B v θ H))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (windowSource p S ψ Z D B v θ H))
      ((fun x=>w x*outerCutoff ψ (sourceRelative p x Z D B v θ H))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,windowSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases ho:outerCutoff ψ (sourceRelative p x Z D B v θ H)=0
  · simp only [ho,ne_eq,not_true_eq_false,ite_false,Function.comp_apply,erase_sourcePoint,
      mul_zero,zero_mul,Finset.sum_const_zero]
  · rw [ite_eq_left ho]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem actual_window_block_support
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (ψ:Fin 4→ℝ→ℂ)(W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)
    (a b A₀ B₀ A₂ B₂:ℝ)(hA₀:0<A₀)(hA₂:0<A₂)
    (hψ₀:∀y,ψ 0 y≠0→y∈Set.Icc A₀ B₀)
    (hψ₂:∀y,ψ 2 y≠0→y∈Set.Icc A₂ B₂)
    (hω₁:∀y∈Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)),ω₁ y=1)
    (hω₂:∀y∈Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)),ω₂ y=1)
    (hV:∀i y,0<y→ retainedCutoffs ψ ω₁ ω₂ i y≠0→V i (Real.log y)=1)
    (Z D B v θ H c₁ c₂ θ₁ θ₂:ℝ)(hZ:0<Z)
    (hW₁:Function.support (clippedSource W₁ c₁ θ₁)⊆Set.Icc a b)
    (hW₂:Function.support (clippedSource W₂ c₂ θ₂)⊆Set.Icc a b) :
    BlockSupport p (pointSource pool (windowSource p S ψ Z D B v θ H))
      W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂ := by
  have hvalid : ∀x∈pointSource pool (windowSource p S ψ Z D B v θ H),Valid x :=
    pointSource_valid pool _ (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
      (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
  have hpos (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i,0< relativeNorm (coordinates p x) Z D B v θ H i :=
    relativeNorm_pos _ (coordinates_pos p hp x (hvalid x hx)) hZ D B v θ H
  refine ⟨?_,?_,?_⟩
  · intro x hx hlive
    have he := fresh_window_eq_one (clippedSource W₁ c₁ θ₁) ω₁ a b A₀ B₀ A₂ B₂
      _ _ _ hW₁ hA₀ hA₂
      (hψ₀ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 0))
      (hψ₂ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 2))
      (hpos x hx 4).le hω₁ hlive
    rw [relative_column_left] at he
    rw [he,star_one]
  · intro x hx hlive
    have he := fresh_window_eq_one (clippedSource W₂ c₂ θ₂) ω₂ a b A₀ B₀ A₂ B₂
      _ _ _ hW₂ hA₀ hA₂
      (hψ₀ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 0))
      (hψ₂ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 2))
      (hpos x hx 5).le hω₂ hlive
    rwa [relative_column_right] at he
  · intro x hx h₁ h₂ i
    apply hV i _ (hpos x hx i)
    apply retainedCutoffs_nonzero ψ ω₁ ω₂ _ ?_ ?_ ?_ i
    · unfold outerCutoff
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 0)
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 1))
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 2))
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 3)
    · rw [relative_column_left]
      exact star_ne_zero.mp h₁
    · rwa [relative_column_right]

end SevenEighths.InverseInitialEnergyCallerWindows

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerEmpty -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerEmpty
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_zero_of_fresh_empty
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Point ι→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D B v θ H m c₁ c₂ θ₁ θ₂:ℝ)(hZ:0<Z)
    (hs:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
    (he:freshColumns p pool ω₁ (Z^(columnCenter D B v))=∅) :
    physicalBlock p hp hcop hg (pointSource pool S) w Ψ j marks
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m=0 := by
  unfold physicalBlock
  apply Finset.sum_eq_zero
  intro x hx
  have hv:=pointSource_valid pool S hdiv hf x hx
  have hleft:x.left⊆pool := by
    obtain ⟨s,hs,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨⟨N,M⟩,hNM,rfl⟩:=Finset.mem_image.mp hx
    exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).1).trans Finset.sdiff_subset
  have hω:ω₁ (columnRatio p x.left Z D B v)=0 := by
    by_contra hn
    rw [columnRatio_actual] at hn
    have hm:= (mem_freshColumns p pool ω₁ (Z^(columnCenter D B v)) x.left).mpr ⟨hleft,hn⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  have hW:clippedSource W₁ c₁ θ₁
      (relativeNorm (coordinates p x) Z D B v θ H 0 *
        relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 4)=0 := by
    by_contra hn
    have hh:=hs.1 x hx hn
    simp only [hω,star_zero] at hh
    exact zero_ne_one hh
  apply Finset.sum_eq_zero
  intro ρ hρ
  rw [physicalTerm_extracted p hp hcop hg hpr Ψ j marks _ _ Φ Z D m x hv ρ,
    physicalKernel_nominal _ _ Φ hZ D B v m θ H _ (coordinates_pos p hp x hv)]
  change w x*(_*(_*secondNormProfile _ _ _ _ _
    (relativeNorm (coordinates p x) Z D B v θ H)))=0
  simp only [secondNormProfile,hW,mul_zero,zero_mul,zero_div]

include hp hcop hg in

theorem physical_nonzero_clipping
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Point ι→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D B v θ H m c₁ c₂ θ₁ θ₂ a b η:ℝ)(hZ:1<Z)(hb:1≤b)
    (hω:Function.support ω₁⊆Set.Icc a b)
    (hs:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
    (ht:Real.log b≤3*η*Real.log Z)
    (hn:physicalBlock p hp hcop hg (pointSource pool S) w Ψ j marks
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m≠0) :
    0≤ max 0 (columnCenter D B v)-columnCenter D B v ∧
      max 0 (columnCenter D B v)-columnCenter D B v≤3*η := by
  apply freshColumns_initial_clipping_shift p hp pool ω₁ a b Z (columnCenter D B v) η hZ hb hω _ ht
  by_contra he
  have he':freshColumns p pool ω₁ (Z^(columnCenter D B v))=∅:=Finset.not_nonempty_iff_eq_empty.mp he
  exact hn (physicalBlock_zero_of_fresh_empty p hp hcop hg hpr pool S hdiv hf w Ψ j marks
    W₁ W₂ ω₁ ω₂ V Φ Z D B v θ H m c₁ c₂ θ₁ θ₂ (zero_lt_one.trans hZ) hs he')

end SevenEighths.InverseInitialEnergyCallerEmpty

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerFixedWindows -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerFixedWindows
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseSecondChildWindows InverseSecondProfileUniform
local notation "Eis"=>ActualEisensteinCubic.O

theorem log_source_support (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W) :
    Function.support (CubicReflectionKernel.logSchwartz W a b ha hs hW)⊆
      Set.Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro x hx
  have hh := hs hx
  change a≤Real.exp x ∧ Real.exp x≤b at hh
  have hl := Real.log_le_log ha hh.1
  have hu := Real.log_le_log (Real.exp_pos x) hh.2
  rw [Real.log_exp] at hl hu
  constructor
  · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]

theorem exists_actual_initial_windows
    (W₁ W₂:ℝ→ℂ)(a b bcap:ℝ)(ha:0<a)(hcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a b)(hs₂:Function.support W₂⊆Set.Icc a b)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (lo hi:Fin 4→ℝ)(hlo:∀i,0<lo i)(hhi:∀i,lo i≤hi i) :
    ∃(wFresh:𝓢(ℝ,ℂ))(V:Fin 6→𝓢(ℝ,ℂ))(M:Fin 6→ℝ)(af bf:ℝ),
      0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      (∀i,0≤M i) ∧ (∀i,HasCompactSupport (V i:ℝ→ℂ)) ∧
      (∀i,Function.support (V i)⊆Set.Icc (-M i) (M i)) ∧
      ∀{ι:Type*}[DecidableEq ι](p:ι→Eis)(_hp:∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
      (_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (ψ:Fin 4→ℝ→ℂ)(_hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
      (Z D B v θ H c₁ c₂ θ₁ θ₂:ℝ),0<Z→1≤ c₁→c₁≤bcap→1≤ c₂→c₂≤bcap→
      BlockSupport p (pointSource pool (windowSource p S ψ Z D B v θ H))
        W₁ W₂ wFresh wFresh (fun i=>V i) Z D B v θ H c₁ c₂ θ₁ θ₂ := by
  let m:=|Real.log a|+|Real.log b|
  obtain ⟨wFresh,V,M,af,bf,haf,hab,hwc,hws,hM,hVc,hVs,hw,hcut⟩ :=
    fixed_windows m bcap lo hi (fun _=>0) (by dsimp [m];positivity) hcap hlo hhi (by simp)
  refine ⟨wFresh,V,M,af,bf,haf,hab,hwc,hws,hM,hVc,hVs,?_⟩
  intro ι _ p hp _ pool S hdiv hf ψ hψ Z D B v θ H c₁ c₂ θ₁ θ₂ hZ hc₁ hb₁ hc₂ hb₂
  let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
  let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
  have hg₁ : Function.support g₁⊆Set.Icc (-m) m := log_source_support W₁ a b ha hs₁ hW₁
  have hg₂ : Function.support g₂⊆Set.Icc (-m) m := log_source_support W₂ a b ha hs₂ hW₂
  have hvalid : ∀x∈pointSource pool (windowSource p S ψ Z D B v θ H),Valid x :=
    pointSource_valid pool _ (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
      (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
  have hpos (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i,0< relativeNorm (coordinates p x) Z D B v θ H i :=
    relativeNorm_pos _ (coordinates_pos p hp x (hvalid x hx)) hZ D B v θ H
  have hblock (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i:Fin 4,relativeNorm (coordinates p x) Z D B v θ H (outerIndex i)∈Set.Icc (lo i) (hi i) :=
    fun i=>hψ i (windowSource_four_nonzero p pool S ψ Z D B v θ H hx i)
  refine ⟨?_,?_,?_⟩
  · intro x hx hn
    have he := hw g₁ hg₁ c₁ θ₁ _ _ _ hc₁ hb₁ (hblock x hx 0) (hblock x hx 2) (hpos x hx 4) ?_
    · rw [relative_column_left] at he
      rw [he,star_one]
    · change positiveSource g₁ c₁ θ₁
        (relativeNorm (coordinates p x) Z D B v θ H 0 *
          relativeNorm (coordinates p x) Z D B v θ H 2 *
          relativeNorm (coordinates p x) Z D B v θ H 4)≠0
      dsimp only [g₁]
      rw [positiveSource_logSchwartz W₁ a b ha hs₁ hW₁ (zero_lt_one.trans_le hc₁)
        (mul_pos (mul_pos (hpos x hx 0) (hpos x hx 2)) (hpos x hx 4))]
      exact hn
  · intro x hx hn
    have he := hw g₂ hg₂ c₂ θ₂ _ _ _ hc₂ hb₂ (hblock x hx 0) (hblock x hx 2) (hpos x hx 5) ?_
    · rwa [relative_column_right] at he
    · change positiveSource g₂ c₂ θ₂
        (relativeNorm (coordinates p x) Z D B v θ H 0 *
          relativeNorm (coordinates p x) Z D B v θ H 2 *
          relativeNorm (coordinates p x) Z D B v θ H 5)≠0
      dsimp only [g₂]
      rw [positiveSource_logSchwartz W₂ a b ha hs₂ hW₂ (zero_lt_one.trans_le hc₂)
        (mul_pos (mul_pos (hpos x hx 0) (hpos x hx 2)) (hpos x hx 5))]
      exact hn
  · intro x hx hl hr i
    have hl' : wFresh (relativeNorm (coordinates p x) Z D B v θ H 4)≠0 := by
      rw [relative_column_left]
      exact star_ne_zero.mp hl
    have hr' : wFresh (relativeNorm (coordinates p x) Z D B v θ H 5)≠0 := by
      rwa [relative_column_right]
    have he := hcut (relativeNorm (coordinates p x) Z D B v θ H) (fun _=>0)
      (by simp) (hblock x hx) hl' hr' i
    simpa only [add_zero,relativeLog] using he

end SevenEighths.InverseInitialEnergyCallerFixedWindows

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindowGeometry -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerWindowGeometry
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialEnergyCallerGeometry
open InverseInitialProfile InverseInitialKernelBridge ConcreteTraceCRT
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

theorem retained_source_windows
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H:ℝ)(hZ:0<Z){x:Source (ι:=ι) 0}
    (hx:x∈windowSource p S ψ Z D B v θ H) :
    ((sourceIdeal p x.common).absNorm:ℝ)≤hi 0*Z^B ∧
    lo 1*Z^θ≤((sourceIdeal p x.divisor).absNorm:ℝ) ∧
    ((sourceIdeal p x.divisor).absNorm:ℝ)≤hi 1*Z^θ ∧
    ((sourceIdeal p x.overlap).absNorm:ℝ)≤hi 2*Z^v ∧
    ‖eisEmbedding x.frequency‖^2≤hi 3*Z^H := by
  have hm : sourcePoint x ∅ ∅∈pointSource ∅ (windowSource p S ψ Z D B v θ H) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,?_⟩
    apply Finset.mem_image.mpr
    exact ⟨(∅,∅),by simp,rfl⟩
  have hh (i:Fin 4) := hψ i (windowSource_four_nonzero p ∅ S ψ Z D B v θ H hm i)
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  change ((sourceIdeal p x.common).absNorm:ℝ)/Z^B∈Set.Icc (lo 0) (hi 0) at h0
  change ((sourceIdeal p x.divisor).absNorm:ℝ)/Z^θ∈Set.Icc (lo 1) (hi 1) at h1
  change ((sourceIdeal p x.overlap).absNorm:ℝ)/Z^v∈Set.Icc (lo 2) (hi 2) at h2
  change ‖eisEmbedding x.frequency‖^2/Z^H∈Set.Icc (lo 3) (hi 3) at h3
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h0.2,
    (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h1.1,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h1.2,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h2.2,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h3.2⟩

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem retained_child_boxes
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))(hhi:∀i,0≤hi i)
    (Z D B v θ H:ℝ)(hZ:0<Z){x:Source (ι:=ι) 0}
    (hx:x∈windowSource p S ψ Z D B v θ H)(u:Eisˣ) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)≤
      (hi 1*hi 2)*Z^(θ+v) ∧
    ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2≤
      (hi 1*hi 3)*Z^(θ+H) := by
  obtain ⟨h0,h1lo,h1,h2,h3⟩ := retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  rw [initial_child_label_norm p,initial_child_row_norm p hp hpr]
  constructor
  · apply (mul_le_mul h1 h2 (by positivity) (mul_nonneg (hhi 1) (Real.rpow_nonneg hZ.le _))).trans_eq
    rw [Real.rpow_add hZ]
    ring
  · apply (mul_le_mul h1 h3 (by positivity) (mul_nonneg (hhi 1) (Real.rpow_nonneg hZ.le _))).trans_eq
    rw [Real.rpow_add hZ]
    ring

omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem retained_source_quotients
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))(hlo:0<lo 1)(hhi:0≤hi 0)
    (Z D B v θ H:ℝ)(hZ:0<Z) :
    ∀t∈InverseInitialQuotientGeometry.quotientSet p (windowSource p S ψ Z D B v θ H),
      (t.absNorm:ℝ)≤(hi 0/lo 1)*Z^(B-θ) := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨h0,h1lo,h1,h2,h3⟩ := retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  rw [InverseInitialQuotientGeometry.quotient_norm_eq p hp x (hdiv x (Finset.mem_filter.mp hx).1)]
  apply (div_le_div₀ (by positivity) h0 (mul_pos hlo (Real.rpow_pos_of_pos hZ _)) h1lo).trans_eq
  rw [Real.rpow_sub hZ]
  ring

end SevenEighths.InverseInitialEnergyCallerWindowGeometry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalDomains -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalDomains
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerWindows InverseInitialEnergyCallerWindowGeometry
open InverseInitialEnergyCallerSourceMask InverseInitialEnergyCallerRanges
open InverseInitialEnergyCallerSource CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem window_power_bounds
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:0<Z)(hhi:∀i,hi i≤Z^η)
    {x:Source (ι:=ι) 0}(hx:x∈windowSource p S ψ Z D B v θ H):
    ((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η) ∧
    ((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η) ∧
    ‖eisEmbedding x.frequency‖^2≤Z^(H+η) := by
  obtain ⟨_,_,hd,hv,hh⟩:=retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  have hpow (i:Fin 4)(r:ℝ):hi i*Z^r≤Z^(r+η):=by
    rw [Real.rpow_add hZ]
    exact (mul_le_mul_of_nonneg_right (hhi i) (Real.rpow_nonneg hZ.le _)).trans_eq (mul_comm _ _)
  exact ⟨hd.trans (hpow 1 θ),hv.trans (hpow 2 v),hh.trans (hpow 3 H)⟩

include hp hcop hg in
theorem actual_window_domains
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:0<Z)(hhi:∀i,hi i≤Z^η):
    ∀x∈coprimeSource p (windowSource p S ψ Z D B v θ H),∀u:Oˣ,
      (initialChild (toTuple p (sectorSource u x))).2.1∈idealRange (Z^(θ+v+2*η)) ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈
        nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)) := by
  apply canonical_child_domains p hp hcop hg hc hpr (windowSource p S ψ Z D B v θ H)
    (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hf x (Finset.mem_filter.mp hx).1) Z θ v H η hZ
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).1
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).2.1
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).2.2

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem retained_quotient_subset
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ):
    quotientSet p (coprimeSource p (windowSource p S ψ Z D B v θ H))⊆
      quotientSet p (windowSource p S ψ Z D B v θ H) :=
  Finset.image_subset_image (Finset.filter_subset _ _)

end SevenEighths.InverseInitialCanonicalDomains

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerState -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerState
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialQuotientGeometry
local notation "Eis"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

omit [DecidableEq ι] in
theorem windowSource_subset_retained
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ) :
    windowSource p S ψ Z D B v θ H ⊆ retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ := by
  intro x hx
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,?_⟩
  have hn := (Finset.mem_filter.mp hx).2
  have hh := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  change ψ 0 (((sourceIdeal p x.common).absNorm:ℝ)/Z^B)*
    ψ 1 (((sourceIdeal p x.divisor).absNorm:ℝ)/Z^θ)≠0 at hh
  simpa only [sourceWeight,one_mul] using hh

theorem window_quotient_subset_retained
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ) :
    quotientSet p (windowSource p S ψ Z D B v θ H) ⊆
      quotientSet p (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ) :=
  Finset.image_subset_image (windowSource_subset_retained p S ψ Z D B v θ H)

theorem initial_F_exact (r z G B θ v:ℝ) :
    max 0 (r+z-2*G-B-v)+(θ+v)=
      initialF r z G (B-θ) (max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v)) := by
  unfold initialF
  ring

variable (hp:∀i,p i≠0)
include hp

theorem actual_window_initial_margins (S : Finset (Source (ι:=ι) 0))
    (ψ : Fin 4 → ℝ → ℂ) (D v H : ℝ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support (ψ 0) ⊆ Set.Icc aC bC)
    (hd : Function.support (ψ 1) ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, λ₀^2 ∣ p i-1)
    {σ : Type*} [DecidableEq σ] (all assigned : Finset σ) (ha : assigned ⊆ all)
    (q : σ → Eis) (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hz : ∀ i ∈ all, 0 ≤ z i) (hq : ∀ i ∈ assigned, q i ≠ 0)
    (hW : ∀ i ∈ assigned, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ assigned, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ assigned, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (windowSource p S ψ Z D B v θ H))
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
  exact retained_initial_margins p hp S (fun _=>1) (ψ 0) (ψ 1)
    aC bC ad bd Z B θ η hZ hC hd hCup hdlo hdiv hpr all assigned ha q z a b W
    hz hq hW hret hthreshold (window_quotient_subset_retained p S ψ Z D B v θ H ht)
    m r δ τ c₁ c₂ h₁ h₂

theorem actual_window_canonical_margins (S : Finset (Source (ι:=ι) 0))
    (ψ : Fin 4 → ℝ → ℂ) (D v H : ℝ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support (ψ 0) ⊆ Set.Icc aC bC)
    (hd : Function.support (ψ 1) ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, λ₀^2 ∣ p i-1)
    {σ : Type*} [DecidableEq σ] (all assigned : Finset σ) (ha : assigned ⊆ all)
    (q : σ → Eis) (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hz : ∀ i ∈ all, 0 ≤ z i) (hq : ∀ i ∈ assigned, q i ≠ 0)
    (hW : ∀ i ∈ assigned, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ assigned, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ assigned, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r τ c₁ c₂ : ℝ)
    (h₁ : r+2*assignedCenter all z ≤ m-c₁)
    (h₂ : 2*r+8*assignedCenter all z ≤ 3*m-c₂)
    (hc:0≤ min c₁ c₂)(hη:η≤ min c₁ c₂/100)(hτ:τ≤ min c₁ c₂/100) :
    CanonicalMargins
      (max 0 (r+assignedCenter all z-2*assignedCenter assigned z-B-v)+(θ+v))
      (initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ)
      (punctureLength Z t (assignedElement assigned q))
      (assignedCenter (all\assigned) z) (3*min c₁ c₂/4) := by
  let δ:=max 0 (r+assignedCenter all z-2*assignedCenter assigned z-B-v)-
    (r+assignedCenter all z-2*assignedCenter assigned z-B-v)
  have hδ:0≤δ:=sub_nonneg.mpr (le_max_right _ _)
  obtain ⟨h1,h2⟩ := actual_window_initial_margins p hp S ψ D v H
    aC bC ad bd Z B θ η hZ hC hd hCup hdlo hdiv hpr all assigned ha q z a b W
    hz hq hW hret hthreshold ht m r δ τ c₁ c₂ h₁ h₂
  rw [initial_F_exact]
  change CanonicalMargins (initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ)
    _ _ _ _
  have hc1:=min_le_left c₁ c₂
  have hc2:=min_le_right c₁ c₂
  constructor <;> linarith

end SevenEighths.InverseInitialEnergyCallerState

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalState -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerWindowGeometry InverseInitialEnergyCallerGeometry
open InverseInitialEnergyCallerRanges CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda

def fullPunctureWidth (Z:ℝ)(t:Ideal O)(j:O):ℝ :=
  Real.logb Z (Ideal.absNorm (Ideal.span {j*primaryGenerator t}):ℝ)

theorem full_puncture_width_exact (Z:ℝ)(hZ:1<Z)(t:Ideal O)(j:O)
    (hm:j*primaryGenerator t≠0):
    0≤fullPunctureWidth Z t j ∧
      ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) := by
  have hn:(1:ℝ)≤Ideal.absNorm (Ideal.span {j*primaryGenerator t}) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hm))
  constructor
  · unfold fullPunctureWidth Real.logb
    exact div_nonneg (Real.log_nonneg hn) (Real.log_pos hZ).le
  · rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact (Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (zero_lt_one.trans_le hn)).symm

theorem full_product_width_bound (Z P G η:ℝ)(hZ:1<Z)(t:Ideal O)(j:O)
    (hm:j*primaryGenerator t≠0)
    (hspan:Ideal.span {j*primaryGenerator t}=t*Ideal.span {j})
    (ht:(t.absNorm:ℝ)≤Z^(P+2*η))
    (hj:(Ideal.absNorm (Ideal.span {j}):ℝ)≤Z^(G+η)):
    fullPunctureWidth Z t j≤P+G+3*η := by
  have hz:=zero_lt_one.trans hZ
  have hpos:0<(Ideal.absNorm (Ideal.span {j*primaryGenerator t}):ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hm))
  have hb:(Ideal.absNorm (Ideal.span {j*primaryGenerator t}):ℝ)≤Z^(P+G+3*η):=by
    rw [hspan,map_mul,Nat.cast_mul]
    apply (mul_le_mul ht hj (by positivity) (Real.rpow_nonneg hz.le _)).trans_eq
    rw [←Real.rpow_add hz]
    congr 1
    ring
  unfold fullPunctureWidth Real.logb
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  simpa only [Real.log_rpow hz] using Real.log_le_log hpos hb

theorem physical_row_width_le (m r z G B θ H η τ:ℝ)
    (hcut:radialCenter m H θ (r+z-2*G) B≤4*η+τ):
    θ+H+2*η≤ initialM m r z G (B-θ) η τ := by
  unfold radialCenter at hcut
  unfold initialM
  linarith

theorem enlarged_initial_margins (m r z G B θ v H η τ Q c₁ c₂:ℝ)
    (h₁:r+2*z≤ m-c₁)(h₂:2*r+8*z≤3*m-c₂)
    (hG:0≤G)(hP:-2*η≤B-θ)(hQ:Q≤B-θ+G+3*η)
    (hc:0≤ min c₁ c₂)(hη:0≤η)(hηsmall:η≤ min c₁ c₂/100)
    (hτ:τ≤ min c₁ c₂/100)
    (hcut:radialCenter m H θ (r+z-2*G) B≤4*η+τ):
    CanonicalMargins
      (max 0 (r+z-2*G-B-v)+(θ+v+2*η)) (θ+H+2*η) Q (z-G)
      (3*min c₁ c₂/4) := by
  have hd:0≤ max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v):=
    sub_nonneg.mpr (le_max_right _ _)
  have hh:=initial_margins (delta:=max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v))
    h₁ h₂ hG hP hQ hc hd hηsmall hτ
  have hr:=physical_row_width_le m r z G B θ H η τ hcut
  unfold CanonicalMargins at hh ⊢
  unfold initialF at hh
  constructor <;> linarith [hh.1,hh.2]

theorem enlarged_label_exact (N V η:ℝ)(hV:0≤V+2*η):
    max 0 (V+2*η)=V+2*η ∧
      N+max 0 (V+2*η)-(N+V)=2*η := by
  rw [max_eq_right hV]
  exact ⟨rfl,by ring⟩

theorem assigned_label_weight_le {σ:Type*}[DecidableEq σ]
    (slots J₁ J₂:Finset σ)(K:ℕ)(hK:slots.card≤K)
    (h₁:J₁⊆slots)(h₂:J₂⊆slots)(f:Ideal O)(hf:f≠0):
    ((IdealMobiusDivisorSum.idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1)≤ secondLabelWeight K f := by
  have hmem:(1:Ideal O)∈IdealMobiusDivisorSum.idealDivisors f:=
    (IdealMobiusDivisorSum.mem_idealDivisors hf).mpr (one_dvd _)
  have hn:(1:ℝ)≤(IdealMobiusDivisorSum.idealDivisors f).card:=by
    exact_mod_cast Finset.one_le_card.mpr ⟨1,hmem⟩
  have hcard1:=Finset.card_le_card h₁
  have hcard2:=Finset.card_le_card h₂
  exact pow_le_pow_right₀ hn (by omega)

end SevenEighths.InverseInitialCanonicalState

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalStateSource -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerWindowGeometry InverseInitialEnergyCallerGeometry
open InverseInitialEnergyCallerRanges CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem live_widths_nonnegative
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:1<Z)(hhi:∀i,hi i≤Z^η)
    {x:Source (ι:=ι) 0}(hx:x∈windowSource p S ψ Z D B v θ H)
    (hf:x.frequency≠0):
    0≤θ+v+2*η ∧ 0≤θ+H+2*η := by
  have hz:=zero_lt_one.trans hZ
  obtain ⟨_,_,hd,hv,hh⟩:=retained_source_windows p S ψ lo hi hψ Z D B v θ H hz hx
  have bound (a c:ℝ)(i:Fin 4)(ha:a≤hi i*Z^c):a≤Z^(c+η):=by
    apply (ha.trans (mul_le_mul_of_nonneg_right (hhi i) (Real.rpow_nonneg hz.le c))).trans_eq
    rw [←Real.rpow_add hz]
    congr 1
    ring
  obtain ⟨hlabel,hrow⟩:=initial_child_enclosures p hp hpr x 1 Z θ v H η hz
    (bound _ _ 1 hd) (bound _ _ 2 hv) (bound _ _ 3 hh)
  have hI:(1:ℝ)≤Ideal.absNorm (initialChild (toTuple p (sectorSource 1 x))).2.1:=by
    have hne:(initialChild (toTuple p (sectorSource 1 x))).2.1≠0:=
      mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hne)
  have hdiv:(1:ℝ)≤(sourceIdeal p x.divisor).absNorm:=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _))
  have hfreq:(1:ℝ)≤‖eisEmbedding x.frequency‖^2:=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hf))
  have hr:(1:ℝ)≤‖eisEmbedding (initialChild (toTuple p (sectorSource 1 x))).2.2‖^2:=by
    rw [initial_child_row_norm p hp hpr]
    exact one_le_mul_of_one_le_of_one_le hdiv hfreq
  constructor
  · exact (Real.rpow_le_rpow_left_iff hZ).mp
      (by simpa only [Real.rpow_zero] using hI.trans hlabel)
  · exact (Real.rpow_le_rpow_left_iff hZ).mp
      (by simpa only [Real.rpow_zero] using hr.trans hrow)

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem retained_full_puncture
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(D v H aC bC ad bd Z B θ η G:ℝ)(hZ:1<Z)
    (hC:Function.support (ψ 0)⊆Set.Icc aC bC)
    (hd:Function.support (ψ 1)⊆Set.Icc ad bd)
    (hCup:bC≤Z^η)(hdlo:Z^(-η)≤ad)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (j:O)(hj:j≠0)(hnj:(Ideal.absNorm (Ideal.span {j}):ℝ)≤Z^(G+η))
    {t:Ideal O}(ht:t∈quotientSet p (windowSource p S ψ Z D B v θ H)):
    j*primaryGenerator t≠0 ∧ 0≤fullPunctureWidth Z t j ∧
    ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
    fullPunctureWidth Z t j≤B-θ+G+3*η := by
  have hspan:=span_source_puncture p hp (windowSource p S ψ Z D B v θ H) hpr j ht
  have ht0:=quotientSet_nonzero p hp (windowSource p S ψ Z D B v θ H) t ht
  have hm:j*primaryGenerator t≠0:=by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [hspan]
    exact mul_ne_zero ht0 (Ideal.span_singleton_eq_bot.not.mpr hj)
  have hret:=window_quotient_subset_retained p S ψ Z D B v θ H ht
  have hnt:=retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
    aC bC ad bd Z B θ η (zero_lt_one.trans hZ) hC hd hCup hdlo hdiv t hret
  obtain ⟨hn,he⟩:=full_puncture_width_exact Z hZ t j hm
  exact ⟨hm,hn,he,full_product_width_bound Z (B-θ) G η hZ t j hm hspan hnt hnj⟩

end SevenEighths.InverseInitialCanonicalState

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalStateWindow -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_window_state
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:1<Z)(hη:0≤η)
    (hhi:∀i,hi i≤Z^η)(hdlo:Z^(-η)≤lo 1)
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    {σ:Type*}[DecidableEq σ](all assigned:Finset σ)(hassigned:assigned⊆all)
    (q:σ→O)(z a b:σ→ℝ)(W:σ→ℝ→ℂ)
    (hz:∀i∈all,0≤z i)(hq:∀i∈assigned,q i≠0)
    (hW:∀i∈assigned,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hret:∀i∈assigned,W i ((Ideal.absNorm (Ideal.span {q i}):ℝ)/Z^(z i))≠0)
    (hthreshold:(∏i∈assigned,b i)≤Z^η)
    {t:Ideal O}(ht:t∈quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r τ c₁ c₂:ℝ)(hD:D=r+assignedCenter all z-2*assignedCenter assigned z)
    (h₁:r+2*assignedCenter all z≤ m-c₁)
    (h₂:2*r+8*assignedCenter all z≤3*m-c₂)
    (hc:0≤ min c₁ c₂)(hηsmall:η≤ min c₁ c₂/100)(hτ:τ≤ min c₁ c₂/100)
    (hcut:radialCenter m H θ D B≤4*η+τ)
    (hclip:max 0 (D-B-v)-(D-B-v)≤3*η):
    let N:=max 0 (D-B-v)
    let V:=θ+v+2*η
    let M:=θ+H+2*η
    let j:=assignedElement assigned q
    j*primaryGenerator t≠0 ∧ 0≤N ∧ 0≤V ∧ 0≤M ∧
    0≤fullPunctureWidth Z t j ∧
    ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
    CanonicalMargins (N+V) M (fullPunctureWidth Z t j)
      (assignedCenter (all\assigned) z+η) (min c₁ c₂/2) ∧
    N+V≤ r+assignedCenter all z+7*η ∧
    M≤ r+assignedCenter all z+7*η ∧
    N+V-(N+(θ+v))=2*η := by
  dsimp only
  have hretained:=window_quotient_subset_retained p S ψ Z D B v θ H ht
  have hP: -2*η≤B-θ:=by
    have hn:=(nonempty_radius p hp (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ)
      Z (B-θ) η hZ ⟨t,hretained⟩
      (retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
        (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZ)
        (hψ 0) (hψ 1) (hhi 0) hdlo hdiv)).2
    linarith
  have hreg:=assigned_register all assigned hassigned z hz
  have hj:assignedElement assigned q≠0:=Finset.prod_ne_zero_iff.mpr hq
  have hnj:=assigned_norm_power assigned q z a b W Z η (zero_lt_one.trans hZ) hW hret hthreshold
  obtain ⟨hm,hQ0,hnorm,hQ⟩:=retained_full_puncture p hp hpr S ψ D v H
    (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (assignedCenter assigned z) hZ
    (hψ 0) (hψ 1) (hhi 0) hdlo hdiv (assignedElement assigned q) hj hnj ht
  obtain ⟨x,hx,hxt⟩:=Finset.mem_image.mp ht
  obtain ⟨hV,hM⟩:=live_widths_nonnegative p hp hpr S ψ lo hi hψ Z D B v θ H η hZ hhi
    hx (hf x (Finset.mem_filter.mp hx).1)
  have hmg:=enlarged_initial_margins m r (assignedCenter all z) (assignedCenter assigned z)
    B θ v H η τ (fullPunctureWidth Z t (assignedElement assigned q)) c₁ c₂
    h₁ h₂ hreg.1 hP hQ hc hη hηsmall hτ (by simpa only [hD] using hcut)
  rw [←hD,hreg.2.2] at hmg
  have hactual:CanonicalMargins (max 0 (D-B-v)+(θ+v+2*η)) (θ+H+2*η)
      (fullPunctureWidth Z t (assignedElement assigned q))
      (assignedCenter (all\assigned) z+η) (min c₁ c₂/2):=by
    unfold CanonicalMargins at hmg ⊢
    constructor <;> linarith [hmg.1,hmg.2]
  have hF:max 0 (D-B-v)+(θ+v+2*η)≤ r+assignedCenter all z+7*η:=by
    rw [hD] at hclip ⊢
    linarith [hreg.1]
  have hMF:θ+H+2*η≤ max 0 (D-B-v)+(θ+v+2*η):=by
    have hh:=hactual.1
    linarith [hreg.2.1]
  exact ⟨hm,le_max_left _ _,hV,hM,hQ0,hnorm,hactual,hF,hMF.trans hF,by ring⟩

end SevenEighths.InverseInitialCanonicalState

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialRetainedPhysical -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialRetainedPhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseReflectedPhase InverseMoment InverseInitialClippedColumns
open CanonicalCoefficientClass ConcreteTraceCRT SecondPassArithmetic FirstPassCubeLabels IdealMobiusDivisorSum
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerModes
open InverseInitialQuotientGeometry InverseInitialEnergyCallerGeometry InverseInitialCanonicalState
local notation "O"=>ActualEisensteinCubic.O

theorem retained_physical_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(Vlog:Fin 6→ℝ→ℂ)(Mlog:Fin 6→ℝ)
    (hVlog:∀i,ContDiff ℝ ∞ (Vlog i))(hSlog:∀i,HasCompactSupport (Vlog i))
    (hMlog:∀i,0≤Mlog i)(hbox:∀i y,Vlog i y≠0→|y|≤Mlog i)
    (ω₁ ω₂:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hω₁:Function.support ω₁⊆Set.Icc lo b)(hω₂:Function.support ω₂⊆Set.Icc lo b)
    (hd₁:ContDiff ℝ ∞ ω₁)(hd₂:ContDiff ℝ ∞ ω₂)
    (cap margin eps U π:ℝ)(hcap:0≤ cap)(hmargin:0< margin)(heps:0<eps)(hU:0≤U)(hπ:0<π)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧ ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](slots:Finset σ),slots.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(a:σ→primePool F→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,1≤Hslot i)→
      (∀i∈slots,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1)→∀z:ℝ,0≤z→(∏i∈slots,Hslot i)≤Z^z→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
    ∀(j:O)(D B v θ H R m η:ℝ),R≤U→0≤η→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),0<c₁→0<c₂→
      BlockSupport p (pointSource Finset.univ S) W₁ W₂ ω₁ ω₂ Vlog Z D B v θ H c₁ c₂ θ₁ θ₂→
      (∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
    ∀(labels:Finset (Ideal O))(rows:Finset O),
      (∀f∈labels,Admissible f ∧ (f.absNorm:ℝ)≤Z^(θ+v+2*η))→
      rows⊆nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η))→(∀k∈rows,-k∈rows)→
      (∀x∈S,(initialChild (toTuple p (sectorSource
        (unitSector p hp (InverseInitialRayAttachment.poolPrimary_primary F hF) (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource
        (unitSector p hp (InverseInitialRayAttachment.poolPrimary_primary F hF) (sourcePoint x ∅ ∅)) x))).2.2∈rows)→
      max 0 (columnCenter D B v)-columnCenter D B v≤3*η→R=B-θ+2*η→
      (∀t∈quotientSet p S,
        j*primaryGenerator t≠0 ∧ 0≤θ+v+2*η ∧ 0≤θ+H+2*η ∧
        0≤fullPunctureWidth Z t j ∧
        ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
        θ+H+2*η≤ cap ∧ max 0 (columnCenter D B v)+(θ+v+2*η)≤ cap ∧
        CanonicalMargins (max 0 (columnCenter D B v)+(θ+v+2*η))
          (θ+H+2*η) (fullPunctureWidth Z t j) z margin)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ S) (w∘erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+15*η+π+eps)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨fresh₁,fresh₂,hsf₁,hsf₂,hphysical⟩:=
    InverseInitialEnergyCallerReference.actual_physical_reference_bound
      W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ Vlog Mlog hVlog hSlog hMlog hbox
      ω₁ ω₂ lo b hlo hb hω₁ hω₂ hd₁ hd₂
  obtain ⟨af₁,bf₁,haf₁,hab₁,_,hs₁f⟩:=hsf₁
  obtain ⟨af₂,bf₂,haf₂,hab₂,_,hs₂f⟩:=hsf₂
  obtain ⟨J₁,B₁,hB₁,hm₁⟩:=canonical_marked_energy_exists cap cap margin eps hcap hcap hmargin heps
    K fresh₁ af₁ bf₁ haf₁ (haf₁.le.trans hab₁) (subset_trans (subset_closure) hs₁f)
  obtain ⟨J₂,B₂,hB₂,hm₂⟩:=canonical_marked_energy_exists cap cap margin eps hcap hcap hmargin heps
    K fresh₂ af₂ bf₂ haf₂ (haf₂.le.trans hab₂) (subset_trans (subset_closure) hs₂f)
  let J:=J₁+J₂
  obtain ⟨Cp,hCp,hphysical⟩:=hphysical J K U π hU hπ
  refine ⟨J,B₁+B₂,by linarith,?_⟩
  intro q hq
  obtain ⟨C₁,Z₁,hC₁,hZ₁,hm₁⟩:=hm₁ q hq
  obtain ⟨C₂,Z₂,hC₂,hZ₂,hm₂⟩:=hm₂ q hq
  refine ⟨Cp*(C₁+C₂),max Z₁ Z₂,mul_pos hCp (add_pos hC₁ hC₂),lt_max_of_lt_left hZ₁,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec slots hslots lists Hslot a hdis hHslot hP ha z hz hprod Ψ hΨ hperiod
    S hdiv hf j D B v θ H R m η hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn w hw labels rows hlabels hrows hneg hchild hclip hReq hstate
  have hZp:1<Z:=hZ₁.trans_le ((le_max_left _ _).trans hZ)
  have hD₁:B₁*Z^(cap+1)≤Dpool:=
    (mul_le_mul_of_nonneg_right (by linarith : B₁≤B₁+B₂) (Real.rpow_nonneg (by linarith) _)).trans hD
  have hD₂:B₂*Z^(cap+1)≤Dpool:=
    (mul_le_mul_of_nonneg_right (by linarith : B₂≤B₁+B₂) (Real.rpow_nonneg (by linarith) _)).trans hD
  have hmoment₁:=hm₁ Z ((le_max_left _ _).trans hZ) Dpool hD₁ slots hslots lists Hslot a hdis hHslot hP ha z hz hprod Ψ hΨ hperiod
  have hmoment₂:=hm₂ Z ((le_max_right _ _).trans hZ) Dpool hD₂ slots hslots lists Hslot a hdis hHslot hP ha z hz hprod Ψ hΨ hperiod
  have hbound:=hphysical p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) (poolPrimary_odd F hFa)
    S hdiv hf Finset.univ Ψ hΨ j slots hslots lists a ha
    Z D B v θ H R m η hZp hR (mul_nonneg hη (Real.log_pos hZp).le)
    c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn w hw labels rows
    (fun f hf=>(hlabels f hf).1.1) hneg hchild
    (max 0 (columnCenter D B v)+(θ+v)) (C₁+C₂) (eps+4*η) (by positivity) hclip
    (by unfold columnCenter;ring) hReq ?_
  · convert hbound using 1
    rw [show m+11*η+π+(eps+4*η)=m+15*η+π+eps by ring]
    ring
  · intro s ρ A₁ hA₁ A₂ hA₂ t ht
    obtain ⟨hm,hV,hM,hQ,hnorm,hMc,hFc,hmargin⟩:=hstate t ht
    have hweight:∀f∈labels,((idealDivisors f).card:ℝ)^(A₁.card+A₂.card+1)≤ secondLabelWeight K f:=by
      intro f hf
      exact assigned_label_weight_le slots A₁ A₂ K hslots (Finset.mem_powerset.mp hA₁)
        (Finset.mem_powerset.mp hA₂) f (hlabels f hf).1.1
    have hleft:=InverseInitialCanonicalEnergy.initial_child_from_rank p hp hcop hg Finset.univ Ψ
      (secondRayMinus Ψ ρ) slots (slots\A₁) lists a fresh₁ Z cap cap z margin eps C₁
      (max 0 (columnCenter D B v)) (θ+v) (θ+H+2*η) (fullPunctureWidth Z t j) η K J₁
      (j*primaryGenerator t) hZp ((show IsBaseRayTwist Ψ Ψ from Or.inl rfl).secondMinus ρ) hm
      (le_max_left _ _) hV hM hQ hMc hFc hmargin hnorm Finset.sdiff_subset labels hlabels rows hrows
      _ (by intros;positivity) hweight s hmoment₁
    have hright:=InverseInitialCanonicalEnergy.initial_child_from_rank p hp hcop hg Finset.univ Ψ
      (secondRayPlus Ψ ρ) slots (slots\A₂) lists a fresh₂ Z cap cap z margin eps C₂
      (max 0 (columnCenter D B v)) (θ+v) (θ+H+2*η) (fullPunctureWidth Z t j) η K J₂
      (j*primaryGenerator t) hZp ((show IsBaseRayTwist Ψ Ψ from Or.inl rfl).secondPlus ρ) hm
      (le_max_left _ _) hV hM hQ hMc hFc hmargin hnorm Finset.sdiff_subset labels hlabels rows hrows
      _ (by intros;positivity) hweight s hmoment₂
    constructor
    · apply hleft.trans
      have hexp:max 0 (columnCenter D B v)+(θ+v)+eps+4*η=
        max 0 (columnCenter D B v)+(θ+v)+(eps+4*η):=by ring
      rw [hexp]
      gcongr
      · linarith
      · linarith [norm_nonneg s]
      · dsimp [J]; omega
    · apply hright.trans
      have hexp:max 0 (columnCenter D B v)+(θ+v)+eps+4*η=
        max 0 (columnCenter D B v)+(θ+v)+(eps+4*η):=by ring
      rw [hexp]
      gcongr
      · linarith
      · linarith [norm_nonneg s]
      · dsimp [J]; omega

end SevenEighths.InverseInitialRetainedPhysical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialRetainedWindow -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialRetainedWindow
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerSourceMask InverseInitialQuotientGeometry InverseInitialClippedColumns
open InverseInitialCanonicalState InverseInitialEnergyCallerState FirstPassCubeLabels
local notation "O"=>ActualEisensteinCubic.O

theorem retained_window_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (lo hi:Fin 4→ℝ)(hlo:∀i,0<lo i)(hhi:∀i,lo i≤hi i)
    (cap gap eps U π:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hU:0≤U)(hπ:0<π)(K:ℕ):
    ∃degree:ℕ,∃Btree Tclip:ℝ,1≤Btree ∧ 0≤Tclip ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
    ∀(ψ:Fin 4→ℝ→ℂ),(∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))→
    ∀(D B v θ H m r η τ:ℝ),0≤η→η≤gap/50→τ≤gap/50→
      (∀i,hi i≤Z^η)→Z^(-η)≤lo 1→Tclip≤3*η*Real.log Z→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→B-θ+2*η≤U→
      radialCenter m H θ D B≤4*η+τ→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤ c₁→c₁≤bcap→1≤ c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ (windowSource p S ψ Z D B v θ H))
        (w∘erasePoint) Ψ (assignedElement assigned qelem)
        (primeMark (all\assigned) lists coeff)
        (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+15*η+π+eps)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨fresh,Vlog,Mlog,af,bf,haf,hab,hfc,hfs,hM,hVc,hVs,hwindow⟩:=
    InverseInitialEnergyCallerFixedWindows.exists_actual_initial_windows
      W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ lo hi hlo hhi
  have hfs':Function.support (fresh:ℝ→ℂ)⊆Set.Icc af (max 1 bf):=by
    intro x hx
    have h:=hfs (subset_closure hx)
    exact ⟨h.1,h.2.trans (le_max_right _ _)⟩
  obtain ⟨J,Btree,hBtree,hbound⟩:=InverseInitialRetainedPhysical.retained_physical_bound
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ (fun i=>Vlog i) Mlog
    (fun i=>(Vlog i).smooth ⊤) hVc hM (fun i y hy=>abs_le.mpr (hVs i hy))
    fresh fresh af (max 1 bf) haf (le_max_left _ _) hfs' hfs' (fresh.smooth ⊤) (fresh.smooth ⊤)
    cap gap eps U π hcap hgap heps hU hπ K
  refine ⟨J,Btree,Real.log (max 1 bf),hBtree,Real.log_nonneg (le_max_left _ _),?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,hbound⟩:=hbound q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf ψ hψ
    D B v θ H m r η τ hη hηsmall hτ hhiZ hloZ hlog hprodj hprod hDeq hmargin₁ hmargin₂ hparent hR hrad
    c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  have hZp:1<Z:=hZ₀.trans_le hZ
  have hprimary:=InverseInitialRayAttachment.poolPrimary_primary F hFa
  let Sw:=windowSource p S ψ Z D B v θ H
  let Sc:=coprimeSource p Sw
  have hdivw:∀x∈Sw,x.divisor⊆x.common:=fun x hx=>hdiv x (Finset.mem_filter.mp hx).1
  have hfw:∀x∈Sw,x.frequency≠0:=fun x hx=>hf x (Finset.mem_filter.mp hx).1
  have hdivc:∀x∈Sc,x.divisor⊆x.common:=fun x hx=>hdivw x (Finset.mem_filter.mp hx).1
  have hfc':∀x∈Sc,x.frequency≠0:=fun x hx=>hfw x (Finset.mem_filter.mp hx).1
  have hswhole:=hwindow p hp Finset.univ S hdiv hf ψ hψ Z D B v θ H c₁ c₂ θ₁ θ₂
    (zero_lt_one.trans hZp) hc₁ hbc₁ hc₂ hbc₂
  have hpoint:pointSource Finset.univ Sc⊆pointSource Finset.univ Sw:=by
    intro x hx
    obtain ⟨y,hy,hm⟩:=Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨y,(Finset.mem_filter.mp hy).1,hm⟩
  have hsupport:BlockSupport p (pointSource Finset.univ Sc) W₁ W₂ fresh fresh
      (fun i=>Vlog i) Z D B v θ H c₁ c₂ θ₁ θ₂:=
    ⟨fun x hx=>hswhole.1 x (hpoint hx),fun x hx=>hswhole.2.1 x (hpoint hx),
      fun x hx=>hswhole.2.2 x (hpoint hx)⟩
  rw [physicalBlock_coprimeSource p hp hcop hg hprimary Finset.univ _ hdivw hfw]
  by_cases hempty:physicalBlock p hp hcop hg (pointSource Finset.univ Sc) (w∘erasePoint) Ψ
      (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m=0
  · rw [hempty,norm_zero];positivity
  have hclip:= (InverseInitialEnergyCallerEmpty.physical_nonzero_clipping p hp hcop hg
    hprimary Finset.univ Sc hdivc hfc' (w∘erasePoint) Ψ (assignedElement assigned qelem)
    (primeMark (all\assigned) lists coeff) W₁ W₂ fresh fresh (fun i=>Vlog i) Φ
    Z D B v θ H m c₁ c₂ θ₁ θ₂ af (max 1 bf) η hZp (le_max_left _ _) hfs' hsupport hlog hempty).2
  have hqt:quotientSet p Sc⊆quotientSet p Sw:=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hn:∀t∈quotientSet p Sc,(t.absNorm:ℝ)≤Z^(B-θ+2*η):=by
    intro t ht
    exact retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
      (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZp)
      (hψ 0) (hψ 1) (hhiZ 0) hloZ hdiv t
      (window_quotient_subset_retained p S ψ Z D B v θ H (hqt ht))
  have hstates:∀t∈quotientSet p Sc,
      assignedElement assigned qelem*primaryGenerator t≠0 ∧ 0≤θ+v+2*η ∧ 0≤θ+H+2*η ∧
      0≤fullPunctureWidth Z t (assignedElement assigned qelem) ∧
      ‖eisEmbedding (assignedElement assigned qelem*primaryGenerator t)‖^2=
        Z^(fullPunctureWidth Z t (assignedElement assigned qelem)) ∧
      θ+H+2*η≤ cap ∧ max 0 (columnCenter D B v)+(θ+v+2*η)≤ cap ∧
      CanonicalMargins (max 0 (columnCenter D B v)+(θ+v+2*η)) (θ+H+2*η)
        (fullPunctureWidth Z t (assignedElement assigned qelem))
        (assignedCenter (all\assigned) z+η) gap:=by
    intro t ht
    have hs:=actual_window_state p hp hprimary S ψ lo hi hψ Z D B v θ H η hZp hη hhiZ hloZ
      hdiv hf all assigned hassigned qelem z al bl primeW hz hqe hprimeW hprimeLive hprodj (hqt ht)
      m r τ (2*gap) (2*gap) hDeq hmargin₁ hmargin₂ (by simp;positivity)
      (by simp only [min_self];linarith) (by simp only [min_self];linarith) hrad hclip
    simp only [min_self] at hs
    obtain ⟨hm,hN,hV,hM,hQ,he,hmargin,hF,hMr,hshift⟩:=hs
    refine ⟨hm,hV,hM,hQ,he,hMr.trans hparent,hF.trans hparent,?_⟩
    convert hmargin using 1 <;> simp [columnCenter]
  apply hbound Z hZ Dpool hD (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK)
    lists Hslot coeff (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hHs hPs hac
    (assignedCenter (all\assigned) z+η) (by apply add_nonneg _ hη;exact Finset.sum_nonneg (fun i hi=>hz i (Finset.mem_sdiff.mp hi).1))
    hprod Ψ hΨ hperiod Sc hdivc hfc' (assignedElement assigned qelem) D B v θ H (B-θ+2*η) m η
    hR hη c₁ c₂ θ₁ θ₂ (zero_lt_one.trans_le hc₁) (zero_lt_one.trans_le hc₂) hsupport hn w
    (fun x hx=>hw x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
    (idealRange (Z^(θ+v+2*η))) (nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)))
    (fun f hf=>mem_idealRange.mp hf) (Finset.Subset.refl _) ?_ ?_ hclip rfl hstates
  · intro k hk
    exact (child_ball_neg _ k).mpr hk
  · intro x hx
    exact InverseInitialCanonicalDomains.actual_window_domains p hp hcop hg (poolPrimary_odd F hFa)
      hprimary S hdiv hf ψ lo hi hψ Z D B v θ H η (zero_lt_one.trans hZp) hhiZ x hx _

end SevenEighths.InverseInitialRetainedWindow

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.PlainWindowEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentPlainWindowEnergy
open CanonicalQuadraticSieve CenteredMomentRowNorm CenteredMomentPlainEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open HeckeFamily FourierBridge CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem plain_column_integral {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    rowPolynomial S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        rowPolynomial S a (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z := by
  have hi (i : α) : Integrable (fun w : ℝ => β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*CanonicalRowCompletion.idealRowHom z (Ideal.span {a i})) :=
    ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul _).mul_const _
  unfold rowPolynomial
  calc
    _ = ∑ i∈S,∫ w : ℝ,β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*CanonicalRowCompletion.idealRowHom z (Ideal.span {a i}) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_mul_const,integral_const_mul,← height_column_integral V hVc hVs τ _ (ha i).1 t θ X hX]
      ring
    _ = _ := by
      rw [← integral_finsetSum _ (fun i _ => hi i)]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem plain_column_integrable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      rowPolynomial S a (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z) := by
  have hi (i : α) := ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul (β i)).mul_const
    (CanonicalRowCompletion.idealRowHom z (Ideal.span {a i}))
  convert integrable_finsetSum S (fun i _ => hi i) using 1
  funext w
  simp only [rowPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rowEnergy_hasSum_re {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ‖rowPolynomial S a c z‖^2*
      (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rowEnergy S a c U K).re := by
  have hs := Complex.hasSum_re (rowEnergy_summable S a ha c U K hK).hasSum
  simpa only [rowEnergy,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hs

theorem finite_weighted_le_rowEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rows : Finset O) :
    (∑ z∈rows,‖rowPolynomial S a c z‖^2*(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)≤
      (rowEnergy S a c U K).re :=
  sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hU z)) (rowEnergy_hasSum_re S a ha c U K hK)

theorem plain_window_energy_from_shifted {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ w : ℝ,(rowEnergy S a
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K).re≤E*(1+‖w‖)^(2*J)) :
    (rowEnergy S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K).re≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let u := fun z : O => (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re
  let c := fun i => β i*heightCoeff τ t (Ideal.span {a i})*
    CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ
  have hnorm (z : O) (x : ℂ) : ‖(Real.sqrt (u z):ℂ)*x‖^2=u z*‖x‖^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt (hU z)]
  have hfin (rows : Finset O) : (∑ z∈rows,‖rowPolynomial S a c z‖^2*u z)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
    let φ := fun z : rows => fun w : ℝ => (Real.sqrt (u z):ℂ)*
      (logPhase (θ-w) (Real.log X)*rowPolynomial S a
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z)
    have hi (z : rows) : Integrable (fun w => columnDensity V hVc hVs w*φ z w) := by
      have h := (plain_column_integrable S a ha β τ t θ X hX V hVc hVs z).const_mul (Real.sqrt (u z):ℂ)
      convert h using 1
      funext w
      dsimp only [φ]
      ring
    have hb (w : ℝ) : (∑ z : rows,‖φ z w‖^2)≤E*((1+‖w‖)^J)^2 := by
      simp only [φ]
      simp_rw [hnorm]
      simp only [norm_mul,logPhase_norm,one_mul,← pow_mul]
      rw [Finset.sum_coe_sort rows (fun z : O => u z*‖rowPolynomial S a
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)]
      simpa only [mul_comm,Nat.mul_comm] using
        (finite_weighted_le_rowEnergy S a ha _ U K hK hU rows).trans (henergy w)
    have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
      (fun w => (1+‖w‖)^J) (by intro w;positivity) E hE (columnDensity_moments V hVc hVs J) hi hb
    have he (z : rows) : (∫ w : ℝ,columnDensity V hVc hVs w*φ z w)=
        (Real.sqrt (u z):ℂ)*rowPolynomial S a c z := by
      rw [show rowPolynomial S a c z=_ from plain_column_integral S a ha β τ t θ X hX V hVc hVs z,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [φ]
      ring
    simp only [he,hnorm] at hh
    rw [Finset.sum_coe_sort rows (fun z : O => u z*‖rowPolynomial S a c z‖^2)] at hh
    simpa only [mul_comm] using hh
  have hs := rowEnergy_hasSum_re S a ha c U K hK
  rw [← hs.tsum_eq]
  exact Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hU z)) hfin

theorem plain_window_energy_from_height {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ v : ℝ,(rowEnergy S a
      (fun i => β i*heightCoeff τ v (Ideal.span {a i})) U K).re≤E*(1+‖v‖)^(2*J)) :
    (rowEnergy S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K).re≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply plain_window_energy_from_shifted V hVc hVs J S a ha β τ t θ X hX U K hK hU
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow,mul_assoc]

end SevenEighths.CenteredMomentPlainWindowEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ExceptionalWindowPair -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalWindowPair
open CenteredMomentPlainWindowEnergy CenteredMomentRowNorm CenteredMomentSmooth
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem paired_integrals {κ:Type*}(rows:Finset κ)(f g:κ→ℝ→ℂ)
    (hf:∀z∈rows,Integrable (f z))(hg:∀z∈rows,Integrable (g z))
    (a b:ℝ→ℝ)(ha:Integrable a)(hb:Integrable b)
    (_ha0:∀u,0≤a u)(_hb0:∀v,0≤b v)(E:ℝ)(_hE:0≤E)
    (hpair:∀u v,∑z∈rows,‖f z u‖*‖g z v‖≤E*a u*b v):
    (∑z∈rows,‖∫u,f z u‖*‖∫v,g z v‖)≤E*(∫u,a u)*(∫v,b v):=by
  have hinner (u:ℝ):
      (∑z∈rows,‖f z u‖*‖∫v,g z v‖)≤E*a u*(∫v,b v):=by
    calc
      _≤∑z∈rows,‖f z u‖*(∫v,‖g z v‖):=
        Finset.sum_le_sum (fun z hz=>mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm _) (norm_nonneg _))
      _=∫v,∑z∈rows,‖f z u‖*‖g z v‖:=by
        rw [integral_finsetSum _ (fun z hz=>(hg z hz).norm.const_mul _)]
        simp only [integral_const_mul]
      _≤∫v,E*a u*b v:=integral_mono
        (integrable_finsetSum rows (fun z hz=>(hg z hz).norm.const_mul _))
        (hb.const_mul _) (fun v=>hpair u v)
      _=E*a u*(∫v,b v):=integral_const_mul _ _
  calc
    _≤∑z∈rows,(∫u,‖f z u‖)*‖∫v,g z v‖:=
      Finset.sum_le_sum (fun z hz=>mul_le_mul_of_nonneg_right
        (norm_integral_le_integral_norm _) (norm_nonneg _))
    _=∫u,∑z∈rows,‖f z u‖*‖∫v,g z v‖:=by
      rw [integral_finsetSum _ (fun z hz=>(hf z hz).norm.mul_const _)]
      simp only [integral_mul_const]
    _≤∫u,E*a u*(∫v,b v):=integral_mono
      (integrable_finsetSum rows (fun z hz=>(hf z hz).norm.mul_const _))
      ((ha.const_mul E).mul_const _) hinner
    _=E*(∫u,a u)*(∫v,b v):=by rw [integral_mul_const,integral_const_mul]

theorem plain_window_pair {α β:Type*}
    (rows:Finset O)(S:Finset α)(T:Finset β)(a:α→O)(b:β→O)
    (ha:∀i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (hb:∀j,CanonicalQuadraticSieve.Supported (Ideal.span {b j}))
    (c:α→ℂ)(d:β→ℂ)(τ₁ τ₂:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u v:ℝ,(∑z∈rows,
      ‖rowPolynomial S a (fun i=>c i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) z‖*
      ‖rowPolynomial T b (fun j=>d j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) z‖)≤
        E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):
    (∑z∈rows,
      ‖rowPolynomial S a (fun i=>c i*heightCoeff τ₁ t₁ (Ideal.span {a i})*
        columnPhase V₁ (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ₁) z‖*
      ‖rowPolynomial T b (fun j=>d j*heightCoeff τ₂ t₂ (Ideal.span {b j})*
        columnPhase V₂ (Real.log ((Ideal.absNorm (Ideal.span {b j}):ℝ)/Y)) θ₂) z‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫v:ℝ,(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖):=by
  let f:=fun z:O=>fun u:ℝ=>columnDensity V₁ hc₁ hs₁ u*logPhase (θ₁-u) (Real.log X)*
    rowPolynomial S a (fun i=>c i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) z
  let g:=fun z:O=>fun v:ℝ=>columnDensity V₂ hc₂ hs₂ v*logPhase (θ₂-v) (Real.log Y)*
    rowPolynomial T b (fun j=>d j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) z
  have hf (z:O):Integrable (f z):=plain_column_integrable S a ha c τ₁ t₁ θ₁ X hX V₁ hc₁ hs₁ z
  have hg (z:O):Integrable (g z):=plain_column_integrable T b hb d τ₂ t₂ θ₂ Y hY V₂ hc₂ hs₂ z
  have hh:=paired_integrals rows f g (fun z _=>hf z) (fun z _=>hg z)
    (fun u=>(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)
    (fun v=>(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖)
    (columnDensity_moments V₁ hc₁ hs₁ J₁) (columnDensity_moments V₂ hc₂ hs₂ J₂)
    (fun u=>by positivity) (fun v=>by positivity) E hE ?_
  · simpa only [f,g,←plain_column_integral S a ha c τ₁ t₁ θ₁ X hX V₁ hc₁ hs₁,
      ←plain_column_integral T b hb d τ₂ t₂ θ₂ Y hY V₂ hc₂ hs₂] using hh
  · intro u v
    simp only [f,g,norm_mul,logPhase_norm,mul_one]
    calc
      _=(‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ v‖)*
        (∑z∈rows,
          ‖rowPolynomial S a (fun i=>c i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) z‖*
          ‖rowPolynomial T b (fun j=>d j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) z‖):=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _≤(‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ v‖)*
          (E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):=
        mul_le_mul_of_nonneg_left (hpair u v) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _=_:=by ring

end SevenEighths.CenteredMomentExceptionalWindowPair

end

end OAI

end

