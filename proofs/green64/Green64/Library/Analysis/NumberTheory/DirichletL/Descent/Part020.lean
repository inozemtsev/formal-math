module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part017
public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part008

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part020

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.ShortReflectedEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open InverseTerminalWidths InverseReflectedPhase CompletedHeight
local notation "Eis"=>ActualEisensteinCubic.O
universe v

def tupleDivisibilityMark {σ:Type v} [Fintype σ] [DecidableEq σ]
    (lists:σ→Finset (Ideal Eis)) (w:∀i,lists i→ℂ) (A:Ideal Eis):ℂ :=
  ∑p:∀i,lists i,(∏i,w i (p i))*∏i,if (p i).val∣A then (1:ℂ) else 0

theorem completed_tuple_mark {σ:Type v} [Fintype σ] [DecidableEq σ]
    (lists:σ→Finset (Ideal Eis)) (w:∀i,lists i→ℂ)
    (Ψ:Eis→*ℂ) (W:ℝ→ℂ) (hW:HasCompactSupport W)
    (X:ℝ) (hX:0<X) (H:Ideal Eis):
    markedCompletedT Ψ W X (fun A=>tupleDivisibilityMark lists w (H^3*A))=
      ∑p:∀i,lists i,(∏i,w i (p i))*markedCompletedT Ψ W X
        (fun A=>∏i,if (p i).val∣H^3*A then (1:ℂ) else 0) := by
  unfold tupleDivisibilityMark
  rw [markedCompletedT_finset_sum Finset.univ Ψ W hW X hX]
  simp only [markedCompletedT_const_mul]

theorem short_cube_exact_scale (Z N:ℝ) (hZ:1<Z) (H:Ideal Eis) (hH:H≠0):
    Z^(N-3*Real.logb Z (Ideal.absNorm H:ℝ))=Z^N/(Ideal.absNorm H:ℝ)^3 := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:0<(Ideal.absNorm H:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (fun hn=>hH (Ideal.absNorm_eq_zero_iff.mp hn))
  rw [Real.rpow_sub hz,show 3*Real.logb Z (Ideal.absNorm H:ℝ)=Real.logb Z (Ideal.absNorm H:ℝ)*3 by ring,
    show Z^(Real.logb Z (Ideal.absNorm H:ℝ)*3)=(Z^(Real.logb Z (Ideal.absNorm H:ℝ)))^3 from
      Real.rpow_mul_natCast hz.le _ 3,Real.rpow_logb hz (ne_of_gt hZ) hn]

theorem canonical_short_completed_energy (q:ℕ) (hq:q≠0)
    (lo hi:ℝ) (hlo:0<lo) (W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (L cstar eta:ℝ) (hL:0≤L) (hcstar:0<cstar) (heta:0<eta)
    (heta1:eta≤1) (hetac:eta≤ cstar/100000) (rmax:ℕ):
    ∃(degree:ℕ)(C Z₀:ℝ),0<C ∧ 1<Z₀ ∧
    ∀{σ:Type v} [Fintype σ] [DecidableEq σ],∀(F:Ideal Eis)(_hF:Squarefree F)
      (m:Eis)(_hm:m≠0)(Z N V M z₀ margin hcut d:ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hcut≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤d → hcut≤d+eta → d≤ cstar/200 →
    ∀(parents:Finset (Ideal Eis)),(∀I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤ rmax → ∀(lists:σ→Finset (Ideal Eis))(H:σ→ℝ),
      Pairwise (fun i j=>Disjoint (lists i) (lists j)) →
      (∀i,∀P∈lists i,P.IsMaximal) →
      (∀i,∀P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀i,∀P∈lists i,Prime P) → (∀i,∀P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀i,1≤H i) → (∀i,∀P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏i,H i)≤Z^z₀ →
    ∀(Ψ:Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(u:Eisˣ)(θ:ℝ)(w:∀i,lists i→ℂ),(∀i P,‖w i P‖≤1) →
      (∑I∈parents,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64)*(256*(columnDyadicLength (Z^hcut)+1:ℝ))^2 := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩:=canonical_cube_shifted_completed_energy q hq lo hi hlo W hWs hW
    L cstar eta hL hcstar heta heta1 hetac rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  have hZ1:1<Z:=lt_of_lt_of_le hZ₀ hZ
  have hz:0<Z:=zero_lt_one.trans hZ1
  have htw:HasCompactSupport (normTwistedSource W θ):=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((normTwistedSource_support W θ).trans hWs)
  have hcompleted (J:Ideal Eis) (hJ:J∈shortCubeRange (Z^hcut)):
      (∑I∈parents,‖markedCompletedT
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N/(Ideal.absNorm J:ℝ)^3) (fun A=>tupleDivisibilityMark lists w (J^3*A))‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64):=by
    obtain ⟨hJ0,hJnorm⟩:=(mem_shortCubeRange _ J).mp hJ
    have hn:0<(Ideal.absNorm J:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (fun hn=>hJ0 (Ideal.absNorm_eq_zero_iff.mp hn))
    have hc:Real.logb Z (Ideal.absNorm J:ℝ)≤hcut:=
      (Real.logb_le_iff_le_rpow hZ1 hn).mpr hJnorm.le
    have hjpow:(Ideal.absNorm J:ℝ)≤Z^(Real.logb Z (Ideal.absNorm J:ℝ)):=by
      rw [Real.rpow_logb hz (ne_of_gt hZ1) hn]
    have h:=he F hF m hm Z N V M z₀ margin (Real.logb Z (Ideal.absNorm J:ℝ)) d
      hZ hN hM hMc hVc hzc (hc.trans hcutc) hFn hRn hmargin hreserve hVd (hc.trans hcutd) hd
      parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨ hperiod J hJ0 hjpow u θ w hw
    rw [short_cube_exact_scale Z N hZ1 J hJ0] at h
    simpa only [completed_tuple_mark lists w _ _ htw _ (div_pos (Real.rpow_pos_of_pos hz _) (pow_pos hn _)) J] using h
  have hh:=marked_short_completed_energy
    (fun I:parents=>rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (u.val*ConcretePrimeRowBridge.idealGenerator I.val))
    (fun I n=>rowTwist_norm Ψ hΨ _ _ _ n) (fun _=>tupleDivisibilityMark lists w)
    (normTwistedSource W θ) (Z^N) (Z^hcut) (C*(1+‖θ‖)^degree*Z^(N+V-cstar/64))
    (by positivity) (fun J hJ=>by
      rw [Finset.sum_coe_sort parents (fun I:Ideal Eis=>‖markedCompletedT
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N/(Ideal.absNorm J:ℝ)^3) (fun A=>tupleDivisibilityMark lists w (J^3*A))‖^2)]
      exact hcompleted J hJ)
  rw [Finset.sum_coe_sort parents (fun I:Ideal Eis=>‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)] at hh
  exact hh

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ShortReflectedPower -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open InverseTerminalWidths InverseReflectedPhase CompletedHeight
local notation "Eis"=>ActualEisensteinCubic.O
universe v

theorem short_harmonic_small_power (L e:ℝ) (hL:0≤L) (he:0<e):
    ∃C:ℝ,0<C ∧ ∀Z h:ℝ,1≤Z → 0≤h → h≤L →
      (256*(columnDyadicLength (Z^h)+1:ℝ))^2≤C*Z^e := by
  let a:=e/(2*(L+1))
  have ha:0<a:=by dsimp [a]; positivity
  let B:=256*(2+1/(a*Real.log 2))
  have hlog:0<Real.log 2:=Real.log_pos (by norm_num)
  have hB:0<B:=by dsimp [B]; positivity
  refine ⟨B^2,pow_pos hB _,?_⟩
  intro Z h hZ hh hhL
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hZh:1≤Z^h:=Real.one_le_rpow hZ hh
  have hb:=mul_le_mul_of_nonneg_left (columnDyadicLength_small_power a ha (Z^h) hZh)
    (by norm_num:(0:ℝ)≤256)
  have hs:(256*(columnDyadicLength (Z^h)+1:ℝ))^2≤B^2*Z^(h*a*2):=by
    calc
      _≤(B*(Z^h)^a)^2:=pow_le_pow_left₀ (by positivity) (by simpa [B,mul_assoc] using hb) 2
      _=B^2*Z^(h*a*2):=by rw [mul_pow,←Real.rpow_mul hz.le,←Real.rpow_mul_natCast hz.le (h*a) 2]; norm_num
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have heq:a*(2*(L+1))=e:=by dsimp [a]; field_simp
  nlinarith

theorem canonical_short_completed_power_energy (q:ℕ) (hq:q≠0)
    (lo hi:ℝ) (hlo:0<lo) (W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (L cstar eta:ℝ) (hL:0≤L) (hcstar:0<cstar) (heta:0<eta)
    (heta1:eta≤1) (hetac:eta≤ cstar/100000) (rmax:ℕ):
    ∃(degree:ℕ)(C Z₀:ℝ),0<C ∧ 1<Z₀ ∧
    ∀{σ:Type v} [Fintype σ] [DecidableEq σ],∀(F:Ideal Eis)(_hF:Squarefree F)
      (m:Eis)(_hm:m≠0)(Z N V M z₀ margin hcut d:ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤d → hcut≤d+eta → d≤ cstar/200 →
    ∀(parents:Finset (Ideal Eis)),(∀I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤ rmax → ∀(lists:σ→Finset (Ideal Eis))(H:σ→ℝ),
      Pairwise (fun i j=>Disjoint (lists i) (lists j)) →
      (∀i,∀P∈lists i,P.IsMaximal) →
      (∀i,∀P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀i,∀P∈lists i,Prime P) → (∀i,∀P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀i,1≤H i) → (∀i,∀P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏i,H i)≤Z^z₀ →
    ∀(Ψ:Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(u:Eisˣ)(θ:ℝ)(w:∀i,lists i→ℂ),(∀i P,‖w i P‖≤1) →
      (∑I∈parents,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/128) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩:=canonical_short_completed_energy q hq lo hi hlo W hWs hW
    L cstar eta hL hcstar heta heta1 hetac rmax
  obtain ⟨B,hB,hbound⟩:=short_harmonic_small_power L (cstar/128) hL (by positivity)
  refine ⟨degree,C*B,Z₀,mul_pos hC hB,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcut0 hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  have hz:0<Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hh:=he F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  apply hh.trans
  calc
    _≤C*(1+‖θ‖)^degree*Z^(N+V-cstar/64)*(B*Z^(cstar/128)):=
      mul_le_mul_of_nonneg_left (hbound Z hcut (lt_of_lt_of_le hZ₀ hZ).le hcut0 hcutc) (by positivity)
    _=(C*B)*(1+‖θ‖)^degree*Z^(N+V-cstar/128):=by
      rw [show N+V-cstar/128=(N+V-cstar/64)+cstar/128 by ring,Real.rpow_add hz]
      ring

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.ShortCanonicalNormalization -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseShortCanonicalNormalization
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalRowCompletion
open InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis" => ActualEisensteinCubic.O
lemma normalization_norm_sq (Z N V : ℝ) (hZ : 0<Z) (x : ℂ) :
    ‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)*x‖^2 =
      Z^(-V)*‖x‖^2 := by
  have hn : 0≤Z^(-(N+V)/2) := Real.rpow_nonneg hZ.le _
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg hn,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,mul_pow,
    Real.sq_sqrt (Real.rpow_nonneg hZ.le _),←Real.rpow_mul_natCast hZ.le _ 2,
    ←Real.rpow_add hZ]
  congr 2
  norm_num

lemma divisor_weight_sum (K : ℕ) (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z V : ℝ),1≤Z → 0≤V → V≤L →
      ∀ labels : Finset (Ideal Eis),
      (∀ f∈labels,f≠0 ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
      (∑ f∈labels,((idealDivisors f).card:ℝ)^(9+4*K))≤C*Z^(V+ε) := by
  let n : ℕ := 9+4*K
  have hn : (0:ℝ)<n := by dsimp [n]; positivity
  let δ : ℝ := ε/((L+1)*(n:ℝ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨128*D^n,by positivity,?_⟩
  intro Z V hZ hV hVL labels hf
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hbudget : L*(δ*(n:ℝ))≤ε := by
    have heq : (L+1)*(δ*(n:ℝ))=ε := by dsimp [δ]; field_simp
    nlinarith [mul_pos hδ hn]
  have hb (f : Ideal Eis) (hfl : f∈labels) :
      ((idealDivisors f).card:ℝ)^n≤D^n*Z^ε := by
    have hfN : (Ideal.absNorm f:ℝ)≤Z^L :=
      (hf f hfl).2.trans (Real.rpow_le_rpow_of_exponent_le hZ hVL)
    calc
      _ ≤ (D*(Ideal.absNorm f:ℝ)^δ)^n := by gcongr; exact hd f (hf f hfl).1
      _ = D^n*(Ideal.absNorm f:ℝ)^(δ*(n:ℝ)) := by
        rw [mul_pow,Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      _ ≤ D^n*(Z^L)^(δ*(n:ℝ)) := by gcongr
      _ = D^n*Z^(L*(δ*(n:ℝ))) := by rw [←Real.rpow_mul hz.le]
      _ ≤ _ := by gcongr
  have hc := DescentFiberCost.finite_ideal_count_real labels (Z^V)
    (Real.one_le_rpow hZ hV) (fun f hfl => (hf f hfl).1) (fun f hfl => (hf f hfl).2)
  calc
    _ ≤ ∑ _f∈labels,D^n*Z^ε := Finset.sum_le_sum (fun f hfl => hb f hfl)
    _ = (labels.card:ℝ)*(D^n*Z^ε) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (128*Z^V)*(D^n*Z^ε) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (128*D^n)*Z^(V+ε) := by rw [Real.rpow_add hz]; ring

lemma rowTwist_label_transfer (Ψ : Eis→*ℂ) (m a f k : Eis) :
    CanonicalRowCompletion.rowTwist Ψ m (a*f) k =
      CanonicalRowCompletion.rowTwist Ψ m f (a^4*k) := by
  have he : m^6*(a*f)^4*k=m^6*f^4*(a^4*k) := by ring
  unfold CanonicalRowCompletion.rowTwist
  rw [he]

lemma label_eq_rowUnit_generator (f : Ideal Eis) (hf : f≠0) (g : Eis)
    (hg : Ideal.span {g}=f) :
    g=(CompletedUnitRows.rowUnit g).val*ConcretePrimeRowBridge.idealGenerator f := by
  have hgn : g≠0 := by
    intro he
    apply hf
    rw [←hg,he,Ideal.span_singleton_zero]
    rfl
  have hh := CompletedUnitRows.rowUnit_spec g hgn
  rw [hg] at hh
  exact hh.symm

local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
universe v

theorem canonical_short_normalized_generator_energy (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤ cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],
    ∀ (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤d → hcut≤d+eta → d≤ cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀ f∈labels,Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (labelGenerator : Ideal Eis→Eis),(∀ f∈labels,Ideal.span {labelGenerator f}=f) →
    ∀ (T : Finset Eis),(∀ k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) → (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ f∈labels,secondLabelWeight K f * ∑ k∈T,
        ‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)*markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_short_completed_power_energy q hq lo hi hlo W hWs hW
    L cstar eta hL hcstar heta heta1 hetac rmax
  obtain ⟨D,hD,hlabels⟩ := divisor_weight_sum K L (cstar/256) hL (by positivity)
  refine ⟨degree,D*(6*C),Z₀,by positivity,hZ₀,?_⟩
  intro σ _ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabelsN labelGenerator hlabelGenerator T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw
  have hz1 : 1≤Z := (lt_of_lt_of_le hZ₀ hZ).le
  have hz : 0<Z := zero_lt_one.trans_le hz1
  let rows := T.image (fun k => Ideal.span {k})
  have hrows := CompletedUnitRows.image_span_nonzero_norm T (Z^M) hT
  let E := C*(1+‖θ‖)^degree*Z^(N+V-cstar/128)
  have hf (f : Ideal Eis) (hfl : f∈labels) :
      (∑ k∈T,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f) k)
        (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤6*E := by
    let uf := CompletedUnitRows.rowUnit (labelGenerator f)
    have hgf : labelGenerator f=uf.val*ConcretePrimeRowBridge.idealGenerator f :=
      label_eq_rowUnit_generator f (hlabelsN f hfl).1.ne_zero (labelGenerator f) (hlabelGenerator f hfl)
    apply (CompletedUnitRows.sum_nonzero_element_le_units T (fun k hk => (hT k hk).1)
      (fun k => ‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f) k)
        (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)
      (fun k => sq_nonneg _)).trans
    have hb (u : Eisˣ) :
        (∑ I∈rows,‖markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f)
            (u.val*ConcretePrimeRowBridge.idealGenerator I))
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤E := by
      have hh := he f (hlabelsN f hfl).1 m hm Z N V M z₀ margin hcut d
        hZ hN hM hMc hVc hzc hcut0 hcutc (hlabelsN f hfl).2 hRn hmargin hreserve hVd hcutd hd
        rows hrows hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨ hperiod (uf^4*u) θ w hw
      simpa only [hgf,rowTwist_label_transfer,Units.val_mul,Units.val_pow_eq_pow_val,E,mul_assoc] using hh
    calc
      _ ≤ ∑ _u : Eisˣ,E := Finset.sum_le_sum (fun u _ => hb u)
      _ = 6*E := by simp only [Finset.sum_const,Finset.card_univ,CompletedUnitRows.unit_card,nsmul_eq_mul,Nat.cast_ofNat]
  have hl : (∑ f∈labels,secondLabelWeight K f)≤D*Z^(V+cstar/256) :=
    hlabels Z V hz1 hV hVc labels (fun f hfl => ⟨(hlabelsN f hfl).1.ne_zero,(hlabelsN f hfl).2⟩)
  simp_rw [normalization_norm_sq Z N V hz,←Finset.mul_sum]
  calc
    _ ≤ ∑ f∈labels,secondLabelWeight K f*(Z^(-V)*(6*E)) := by
      apply Finset.sum_le_sum
      intro f hfl
      apply mul_le_mul_of_nonneg_left _ (by unfold secondLabelWeight; positivity)
      exact mul_le_mul_of_nonneg_left (hf f hfl) (Real.rpow_nonneg hz.le _)
    _ = (∑ f∈labels,secondLabelWeight K f)*(Z^(-V)*(6*E)) := by rw [Finset.sum_mul]
    _ ≤ (D*Z^(V+cstar/256))*(Z^(-V)*(6*E)) := mul_le_mul_of_nonneg_right hl (by dsimp [E]; positivity)
    _ = (D*(6*C))*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
      dsimp only [E]
      have hr : Z^(V+cstar/256)*Z^(-V)*Z^(N+V-cstar/128)=Z^(N+V-cstar/256) := by
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
      calc
        _ = (D*(6*C))*(1+‖θ‖)^degree*(Z^(V+cstar/256)*Z^(-V)*Z^(N+V-cstar/128)) := by ring
        _ = _ := by rw [hr]

theorem canonical_short_normalized_energy (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤ cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],
    ∀ (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤d → hcut≤d+eta → d≤ cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀ f∈labels,Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (T : Finset Eis),(∀ k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) → (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ f∈labels,secondLabelWeight K f * ∑ k∈T,
        ‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)*markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_short_normalized_generator_energy q hq
    lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax K
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabelsN T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw
  exact he m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc hRn
    hmargin hreserve hVd hcutd hd labels hlabelsN ConcretePrimeRowBridge.idealGenerator
    (fun f _ => ConcretePrimeRowBridge.span_idealGenerator f) T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw

end SevenEighths.InverseShortCanonicalNormalization

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.CanonicalShortAttachment -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseCanonicalShortAttachment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis" => ActualEisensteinCubic.O
universe u v

def idealLists {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (j : σ) : Finset (Ideal Eis) :=
  (lists j).image Subtype.val

def transportCoeff {σ : Type u} (F : Finset (Ideal Eis))
    (a : σ→primePool F→ℂ) (j : σ) (P : Ideal Eis) : ℂ :=
  if h:P∈primePool F then a j ⟨P,h⟩ else 0

@[simp] theorem transportCoeff_val {σ : Type u} (F : Finset (Ideal Eis))
    (a : σ→primePool F→ℂ) (j : σ) (i : primePool F) :
    transportCoeff F a j i.val=a j i := by simp [transportCoeff]

def idealWeights {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (j : σ) (P : idealLists F lists j) : ℂ := transportCoeff F a j P.val

lemma tuple_mark_product {σ : Type u} [Fintype σ] [DecidableEq σ]
    (lists : σ→Finset (Ideal Eis)) (w : ∀j,lists j→ℂ) (A : Ideal Eis) :
    tupleDivisibilityMark lists w A=
      ∏j,∑P:lists j,if P.val∣A then w j P else 0 := by
  unfold tupleDivisibilityMark
  calc
    _ = ∑p:∀j,lists j,∏j,if (p j).val∣A then w j (p j) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j hj
      split_ifs <;> simp
    _ = _ := (Fintype.prod_sum (fun j (P : lists j)=>if P.val∣A then w j P else 0)).symm

theorem indexed_mark_eq_tuple {σ : Type u} [DecidableEq σ]
    (F : Finset (Ideal Eis)) (slots : Finset σ) (lists : σ→Finset (primePool F))
    (a : σ→primePool F→ℂ) (A : Ideal Eis) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a A=
      tupleDivisibilityMark (fun j:slots=>idealLists F lists j.val)
        (fun j:slots=>idealWeights F lists a j.val) A := by
  rw [tuple_mark_product]
  unfold indexedIdealMark
  rw [←Finset.prod_coe_sort slots]
  apply Finset.prod_congr rfl
  intro j hj
  change _ = ∑P:idealLists F lists j.val,if P.val∣A then transportCoeff F a j.val P.val else 0
  rw [Finset.sum_coe_sort (idealLists F lists j.val) (fun P : Ideal Eis=>if P∣A then transportCoeff F a j.val P else 0)]
  change (∑i∈lists j.val,if i.val∣A then a j.val i else 0)=
    ∑P∈(lists j.val).image Subtype.val,if P∣A then transportCoeff F a j.val P else 0
  rw [Finset.sum_image (fun i hi k hk h=>Subtype.ext h)]
  simp only [transportCoeff_val]

lemma idealLists_disjoint {σ : Type u} [DecidableEq σ]
    (F : Finset (Ideal Eis)) (slots : Finset σ) (lists : σ→Finset (primePool F))
    (h : (slots:Set σ).Pairwise (fun j k=>Disjoint (lists j) (lists k))) :
    Pairwise (fun j k:slots=>Disjoint (idealLists F lists j.val) (idealLists F lists k.val)) := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  obtain ⟨i,hi,he⟩:=Finset.mem_image.mp hP
  obtain ⟨i',hi',he'⟩:=Finset.mem_image.mp hQ
  have hii : i=i' := Subtype.ext (he.trans he'.symm)
  have hjk' : j.val≠k.val := fun he=>hjk (Subtype.ext he)
  exact Finset.disjoint_left.mp (h j.property k.property hjk') hi (hii.symm ▸ hi')

lemma idealLists_prime_data {σ : Type u} (F : Finset (Ideal Eis))
    (hF : ∀I∈F,Admissible I) (lists : σ→Finset (primePool F))
    (j : σ) (P : Ideal Eis) (hP : P∈idealLists F lists j) :
    P.IsMaximal ∧ goodLambda∉P ∧ Prime P ∧ ringChar (Eis⧸P)≠2 := by
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
  refine ⟨inferInstance,poolGood F hF i,?_,poolOdd F hF i⟩
  exact Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance

lemma idealLists_capacity {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (H : σ→ℝ)
    (hH : ∀j,∀i∈lists j,(Ideal.absNorm i.val:ℝ)≤H j) :
    ∀j,∀P∈idealLists F lists j,(Ideal.absNorm P:ℝ)≤H j := by
  intro j P hP
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
  exact hH j i hi

lemma idealWeights_norm {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (ha : ∀j,∀i∈lists j,‖a j i‖≤1) :
    ∀j,∀P:idealLists F lists j,‖idealWeights F lists a j P‖≤1 := by
  intro j P
  obtain ⟨i,hi,he⟩:=Finset.mem_image.mp P.property
  change ‖transportCoeff F a j P.val‖≤1
  rw [←he,transportCoeff_val]
  exact ha j i hi

def longReopened (Ψ : Eis→*ℂ) (W : ℝ→ℂ) (X H₀ : ℝ) (mark : Ideal Eis→ℂ) : ℂ :=
  ∑' I:Ideal Eis,∑' B:Ideal Eis,largeCubeCoefficient H₀ B*summand Ψ W X I B*mark (I*B^3)

theorem complete_pool_split {σ : Type u} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (Ψ : Eis→*ℂ) (m f k : Eis) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀x,W x≠0→x≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let mark:=indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    let row:=rowTwist Ψ (m*excludedGenerator S) f k
    outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X=
      (Real.sqrt X:ℂ)*(markedShortCompletedSum row W X H₀ mark+longReopened row W X H₀ mark) := by
  dsimp only
  have hg:=finiteCanonicalMarkedRow_complete_global S D hbad hSp Ψ m f k W b X hX hW hD slots lists a
  change outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X=_ at hg
  have he:=marked_completed_cube_inverse_split (rowTwist Ψ (m*excludedGenerator S) f k)
    W hWc X H₀ hX
    (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)
  rw [←hg] at he
  change (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X=
    markedShortCompletedSum _ W X H₀ _+longReopened _ W X H₀ _ at he
  have hn : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  calc
    _ = (Real.sqrt X:ℂ)*((Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X) := by rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul]
    _ = _ := by rw [he]

lemma complete_pool_sub_long {σ : Type u} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (Ψ : Eis→*ℂ) (m f k : Eis) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀x,W x≠0→x≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let mark:=indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    let row:=rowTwist Ψ (m*excludedGenerator S) f k
    outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X-
      (Real.sqrt X:ℂ)*longReopened row W X H₀ mark=
      (Real.sqrt X:ℂ)*markedShortCompletedSum row W X H₀ mark := by
  dsimp only
  rw [complete_pool_split S D hbad hSp Ψ m f k W hWc b X H₀ hX hW hD slots lists a]
  ring

lemma primary_span (f : Ideal Eis) (hf : Supported f) : Ideal.span {primaryGenerator f}=f :=
  (primaryGenerator_spec f (supported_primaryGenerator_ne_zero f hf)).1

lemma actual_mask (q : ℕ) (m : Eis) :
    m*excludedGenerator (reflectionExcludedPrimes q)=ActualFiber.maskElement q m := rfl

theorem normalized_complete_short_attachment (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤ cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [DecidableEq σ],
    ∀ (m : Eis),m≠0 → ∀ (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤d → hcut≤d+eta → d≤ cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀f∈labels,Supported f ∧ Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (T : Finset Eis),(∀k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
    ∀ D : ℕ,hi*Z^N≤D → ∀ slots : Finset σ,slots.card≤ rmax →
    ∀ (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H : σ→ℝ),
      (slots:Set σ).Pairwise (fun j k=>Disjoint (lists j) (lists k)) →
      (∀j∈slots,1≤H j) → (∀j∈slots,∀i∈lists j,(Ideal.absNorm i.val:ℝ)≤H j) →
      (∏j∈slots,H j)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ)
      (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (∀j∈slots,∀i∈lists j,‖a j i‖≤1) →
      let S:=reflectionExcludedPrimes q
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
      let mark:=indexedIdealMark (fun i:primePool F=>i.val) slots lists a
      (∑f∈labels,secondLabelWeight K f*∑k∈T,
        ‖((Z^(-(N+V)/2):ℝ):ℂ)*
          (outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (primaryGenerator f) k
            slots lists a (normTwistedSource W θ) (Z^N)-
            (Real.sqrt (Z^N):ℂ)*longReopened
              (rowTwist Ψ (ActualFiber.maskElement q m) (primaryGenerator f) k)
              (normTwistedSource W θ) (Z^N) (Z^hcut) mark)‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩:=InverseShortCanonicalNormalization.canonical_short_normalized_generator_energy
    q hq lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax K
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabels T hT D hD slots hcard lists H hdis hH1 hH hprod
    Ψ hΨ hperiod θ a ha
  dsimp only
  let S:=reflectionExcludedPrimes q
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF : ∀I∈F,Admissible I:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
  let ilists:slots→Finset (Ideal Eis):=fun j=>idealLists F lists j.val
  let iw:∀j,ilists j→ℂ:=fun j=>idealWeights F lists a j.val
  have hp (j:slots) (P:Ideal Eis) (hP:P∈ilists j) := idealLists_prime_data F hF lists j.val P hP
  have hcap : ∀j:slots,∀P∈ilists j,(Ideal.absNorm P:ℝ)≤H j.val := by
    intro j P hP
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
    exact hH j.val j.property i hi
  have hw : ∀j:slots,∀P:ilists j,‖iw j P‖≤1 := by
    intro j P
    obtain ⟨i,hi,hh⟩:=Finset.mem_image.mp P.property
    change ‖transportCoeff F a j.val P.val‖≤1
    rw [←hh,transportCoeff_val]
    exact ha j.val j.property i hi
  have henergy:=he (σ:=slots) m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels (fun f hf=>(hlabels f hf).2) primaryGenerator
    (fun f hf=>primary_span f (hlabels f hf).1) T hT (by simpa using hcard)
    ilists (fun j:slots=>H j.val) (idealLists_disjoint F slots lists hdis)
    (fun j P hP=>(hp j P hP).1) (fun j P hP=>(hp j P hP).2.1)
    (fun j P hP=>(hp j P hP).2.2.1) (fun j P hP=>(hp j P hP).2.2.2)
    (fun j=>hH1 j.val j.property) hcap (by simpa only [Finset.prod_coe_sort] using hprod)
    Ψ hΨ hperiod θ iw hw
  have hz : 0<Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hX : 0<Z^N:=Real.rpow_pos_of_pos hz _
  have htw : HasCompactSupport (normTwistedSource W θ):=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((normTwistedSource_support W θ).trans hWs)
  have hupper : ∀x,normTwistedSource W θ x≠0→x≤hi := fun x hx=>
    (hWs (normTwistedSource_support W θ hx)).2
  have hmark : indexedIdealMark (fun i:primePool F=>i.val) slots lists a=
      tupleDivisibilityMark ilists iw := funext (indexed_mark_eq_tuple F slots lists a)
  have hsame (f : Ideal Eis) (k : Eis) :
      outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (primaryGenerator f) k
        slots lists a (normTwistedSource W θ) (Z^N)-
        (Real.sqrt (Z^N):ℂ)*longReopened
          (rowTwist Ψ (ActualFiber.maskElement q m) (primaryGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut)
          (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)=
      (Real.sqrt (Z^N):ℂ)*markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (primaryGenerator f) k)
        (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark ilists iw) := by
    have hh:=complete_pool_sub_long S D (reflectionExcludedPrimes_bad q)
      (reflectionExcludedPrimes_prime q) Ψ m (primaryGenerator f) k
      (normTwistedSource W θ) htw hi (Z^N) (Z^hcut) hX hupper hD slots lists a
    dsimp only at hh
    rw [actual_mask] at hh
    exact hh.trans (by rw [hmark])
  dsimp only [S, F] at hsame
  simp_rw [hsame]
  simpa only [mul_assoc] using henergy

end SevenEighths.InverseCanonicalShortAttachment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.WholeTailUniformDegree -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v

theorem original_family_whole_tail_uniform_degree (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
      (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
      (D : ∀ P : Pset, IsCoprime K P.val →
        ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2) →
      (∀ i,jF i<6) → (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
      (∀ P∈Pset,CubicSieve.Admissible P) →
    ∀ (θ X T QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (∀ P∈Pset,(Ideal.absNorm P:ℝ)≤QP) →
      ‖r K‖≤1 → (∀ P∈Pset,‖aw P‖≤1) →
      ‖literalWholeRow F K hK S jF Pset D s hc W θ X r aw-
        (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
          ∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale F s X QK QP) (16*T),
            literalDyadicRow F K hK S jF Pset D s hc u i W θ X
              (fun K => r K*shapeArgument (primaryGenerator K))
              (fun P => aw P*shapeArgument (primaryGenerator P))‖≤
        (6*‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*Pset.card*
          (C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
            T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹) := by
  obtain ⟨degree,C,hC,hbound⟩ := original_family_row_tail_uniform_degree lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro N a c mode φ σ _ _ F K hK S jF Pset D s hc hN hbase hchar hj hprod hPad θ X T QK QP r aw hX hT hQK hQP hKr hPr hr haw
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  let J := retainedDyads (familyRawScale F s X QK QP) (16*T)
  let rr := fun K => r K*shapeArgument (primaryGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryGenerator P)
  let E := C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
    T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹
  have hb (v : Eisˣ) :
      ‖(∑' i,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa)-
        ∑ i∈J,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa‖≤Pset.card*E :=
    hbound (N:=N) (a:=a) (c:=c) (mode:=mode) F K hK S jF Pset D s hc hN hbase hchar hj hprod v θ X T QK QP rr aa hX hT hQK hQP hKr hPr
      (by simpa only [rr,row_shape_weight_norm r K hK] using hr)
      (fun P hp => by simpa only [aa,slot_shape_weight_norm aw P (hPad P hp)] using haw P hp)
  have hcard : Fintype.card Eisˣ=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact PrimaryIdealUnitReindex.card_units_eq_six
  rw [literalWholeRow_eq_dyadic F K hK S jF Pset D s hc hN hbase hchar hj hprod W lo hi hlo hWs hW θ X hX r aw]
  rw [←mul_sub,norm_mul, norm_mul,stratumShapeFactor_frozen_norm]
  simp only [tsum_fintype]
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ (‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*
        ∑ v : Eisˣ,‖(∑' i,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa)-
          ∑ i∈J,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*∑ _v : Eisˣ,Pset.card*E := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hb v)) (by positivity)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]; dsimp only [E]; ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end

