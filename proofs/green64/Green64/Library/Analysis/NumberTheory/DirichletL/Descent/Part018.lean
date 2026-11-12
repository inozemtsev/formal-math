module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part017
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part013

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part018

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

abbrev exponent := InverseFirstGlobalCaps.dyadicExponent

def columnA (Z : ℝ) (k : SourceIndex) (negative : Bool) : ℝ :=
  exponent Z (k (if negative then 0 else 1))

def columnScale (Z r : ℝ) (k : SourceIndex) (l : ℕ) (negative : Bool) : ℝ :=
  Z^(r-columnA Z k negative-exponent Z (k 2)-exponent Z l)

def secondCutoff (p : ι→O) (Z M r ell V eta tau window : ℝ) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (G E : Finset ι) : ℝ :=
  uniformSecondRadius p Z (exponent Z (k 3)) eta G E
    (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j) (Z^tau)

def source (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :=
  supportedRetainedSource p (extra negative)
    (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
    negative J lists pool (secondCutoff p Z M r ell V eta tau window k l j negative)
    b (columnScale Z r k l negative)

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_valid (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ActualSecondSourceConditions p (source p pool Q k l j negative J lists Z M r ell V eta tau window b) :=
  supported_conditions p hp _ _ (label_parent_valid p pool Q k l j) (fun y _hy=>extra_subset negative y.cube)
    negative J lists pool _ b _

lemma source_frequency_ne_zero (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,x.second.frequency≠0 :=
  supported_frequency_ne_zero p _ _ negative J lists pool _ b _

lemma source_geometry (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*columnScale Z r k l negative :=
  geometrySource_gate p _ b _

include hp in
theorem source_row_gates (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hwindow : Real.exp window≤Z^(4*eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    (∀x∈S,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta (index p x))) ∧
    (∀d∈keys p S,0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d) := by
  intro S
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc : columnScale Z r k l negative*Real.exp window≤
      Z^(r-columnA Z k negative-exponent Z (k 2)-exponent Z l+4*eta) := by
    unfold columnScale
    rw [Real.rpow_add hz]
    exact mul_le_mul_of_nonneg_left hwindow (Real.rpow_nonneg hz.le _)
  exact supported_cell_row_gates p hp _ _ negative J lists pool Z M r ell V (exponent Z (k 3))
    (columnA Z k negative) (exponent Z (k 2)) (exponent Z j) (exponent Z l) eta tau
    (columnScale Z r k l negative*Real.exp window) b (columnScale Z r k l negative)
    hZ heta hbin (by unfold columnScale;positivity) hc

include hp in
theorem source_outer_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap : ℝ)
    (hZ : 1<Z)
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,
      ∀i,outerNorms p x i≤Z^Lcap := by
  exact supported_outer_caps p hp _ _ negative J lists pool Z (exponent Z (k 3)) eta
    (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j)
    tau b (columnScale Z r k l negative) Lcol LY Lcap hZ.le
    (by unfold columnScale;positivity) (by unfold firstCellRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    hcol hYi hgeom hphysical

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepChildren -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_labels (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    (∀d,∀x∈cell p S d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p S d) ∧
    (∀d,∀I∈(actualCellLabels p S d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤
        Z^(actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)) := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_label_gates p hp _ _ negative J lists pool _ b (columnScale Z r k l negative)
    Z (exponent Z (k 2)) (exponent Z j) eta hZ hbin
    (fun y hy=>(hb y hy).2.2.2.1) (fun y hy=>(hb y hy).2.2.2.2.2.2.1)

include hp in
theorem source_child_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (m : O) (hm : m≠0) (Qwidth z c : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hV : 0≤V)
    (hparent : CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d,∀γ∈actualSecondTriples p 1 1 (cell p S d),
      actualSecondInheritedRadicalPuncture m γ≠0 ∧ 0≤actualSecondPunctureWidth Z m γ ∧
      ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
      CanonicalMargins (actualCellTotalExponent Z (columnScale Z r k l negative)
        (exponent Z (k 2)) (exponent Z j) eta d)
        (childM M ell (columnA Z k negative) (exponent Z l) (secondCellExponent Z d 0)
          (secondCellExponent Z d 1) V (exponent Z j) eta)
        (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_child_margins p hp hpr _ _ (label_parent_valid p pool Q k l j)
    (fun y hy=>extra_subset negative y.cube) negative J lists pool _ b m hm
    Z r ell V M Qwidth z c (columnA Z k negative) (exponent Z (k 2)) (exponent Z l) (exponent Z j) eta
    hZ hparent (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) hV
    (dyadic_exponent_nonneg Z hZ _) heta hbin hpuncture
    (fun y hy=>(hb y hy).1) (fun y hy=>(hb y hy).2.1) (fun y hy=>(hb y hy).2.2.2.2.1)

include hp in
theorem source_row_decrease (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b short : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hterminal : short≤ell+V) (hsmall : eta≤ short/16)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d∈keys p S,actualCellRowExponent Z M ell (columnA Z k negative)
      (exponent Z l) V (exponent Z j) eta d+3*short/2≤M := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_row_rank_decrease p hp _ _ (label_parent_valid p pool Q k l j)
    (fun y hy=>extra_subset negative y.cube) negative J lists pool _ b (columnScale Z r k l negative)
    Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta short hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) heta hbin hterminal hsmall
    (fun y hy=>(hb y hy).1) (fun y hy=>(hb y hy).2.1) (fun y hy=>(hb y hy).2.2.2.2.2.1)

include hp in
theorem source_mass_gate (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap eps pi : ℝ)
    (hZ : 1<Z) (heps : 0≤eps)
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap)
    (hbudget : eps*(ell+exponent Z (k 4)/2+exponent Z l+Lcap+11*eta/2)≤pi) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d∈keys p S,eps*(secondCount ell (exponent Z (k 4)) (exponent Z j) (exponent Z l)
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi := by
  intro S
  exact source_cell_mass_gate p hp S (source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b)
    Z Lcap ell (exponent Z (k 4)) (exponent Z j) (exponent Z l) eta eps pi hZ
    (dyadic_exponent_nonneg Z hZ _) heps
    (source_outer_caps p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap
      hZ hcol hYi hgeom hphysical) hbudget

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstCanonicalChildren -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstGlobalCaps InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_total_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)
    (negative:Bool)(J:Finset σ)(lists:σ→Finset ι)(Z M r ell V eta tau window b:ℝ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)):
    let S:=source p pool Q k l j negative J lists Z M r ell V eta tau window b;
    ∀d∈keys p S,actualCellTotalExponent Z (columnScale Z r k l negative)
      (exponent Z (k 2)) (exponent Z j) eta d≤ r+3*ell+V+15*eta :=by
  intro S d hd
  obtain ⟨x,hx⟩:=(mem_keys_iff p S d).mp hd
  have hn:=retained_label_numeric p hp pool Q k l j Z ell eta hZ heta hbin hQ negative J lists
    (secondCutoff p Z M r ell V eta tau window k l j negative) b (columnScale Z r k l negative)
    x (cell_subset p S d hx)
  have he:=actual_cell_child_total_upper p hp S
    (source_valid p hp pool Q k l j negative J lists Z M r ell V eta tau window b)
    (source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b)
    d x hx Z r ell V (columnA Z k negative) (exponent Z (k 2)) (exponent Z l) (exponent Z j) eta b hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) hell hV heta hbin hb hbt
    (source_geometry p pool Q k l j negative J lists Z M r ell V eta tau window b)
    hn.1 hn.2.1 hn.2.2.2.2.2.1
  exact he

include hp in
theorem source_state_bounds (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)
    (negative:Bool)(J:Finset σ)(lists:σ→Finset ι)(Z M r ell V eta tau window b cutoff:ℝ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hterminal:cutoff≤ell+V)(hsmall:eta≤ cutoff/16)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)):
    let S:=source p pool Q k l j negative J lists Z M r ell V eta tau window b;
    ∀d∈keys p S,
      0≤ max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d) ∧
      0≤actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d ∧
      actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d≤ r+3*ell+V+15*eta ∧
      0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d ∧
      actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d+3*cutoff/2≤M :=by
  intro S d hd
  refine ⟨le_max_left _ _,actual_cell_label_nonneg Z _ _ eta d hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) heta,?_,?_,?_⟩
  · exact source_total_cap p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hell hV hb hbt hQ d hd
  · exact (source_row_gates p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hwindow).2 d hd
  · exact source_row_decrease p hp pool Q k l j negative J lists Z M r ell V eta tau window b cutoff hZ heta hbin hterminal hsmall hQ d hd

end SevenEighths.InverseMomentFirstLabelCell

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CanonicalChildSupport -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialArithmetic InverseSecondSourceBlocks InverseSecondFibers
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
variable (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_source_prime_supported (i:ι):Supported (Ideal.span {p i}) :=by
  have hn:(Ideal.span {p i}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr (hp i)
  refine ⟨hn,?_⟩
  intro P hP
  obtain ⟨hprime,hle⟩:=(Ideal.mem_normalizedFactors_iff hn).mp hP
  have he:Ideal.span {p i}=P:=(inferInstance:(Ideal.span {p i}:Ideal O).IsMaximal).eq_of_le hprime.ne_top hle
  subst P
  exact ⟨hg i,hc i⟩

lemma canonical_supported_prod {α:Type*}(S:Finset α)(f:α→Ideal O)
    (hf:∀i∈S,Supported (f i)):Supported (∏i∈S,f i) :=by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Supported (1:Ideal O)
    refine ⟨one_ne_zero,?_⟩
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact (Multiset.notMem_zero P hP).elim
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,supported_mul_iff]
    exact ⟨hf i (Finset.mem_insert_self _ _),ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj))⟩

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_source_ideal_supported (S:Finset ι):Supported (sourceIdeal p S) :=by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  exact canonical_supported_prod S (fun i=>Ideal.span {p i}) (fun i _=>canonical_source_prime_supported p hp hg hc i)

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_prime_product_supported (S:Finset ι)(v:ι→ℕ):Supported (Ideal.span {primeProduct p S v}) :=by
  rw [primeProduct,FiniteGaussPhase.span_finset_prod]
  apply canonical_supported_prod
  intro i hi
  rw [←Ideal.span_singleton_pow]
  exact supported_pow (canonical_source_prime_supported p hp hg hc i) _

include hp hg hc in
lemma actual_second_label_supported {Jo Jn:ℕ}(x:MarkedSecondSource ι Jo Jn):
    Supported (actualSecondChild p 1 1 x).2.1 :=by
  change Supported ((Ideal.span {(jLabel p x.cube.support
    (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)})*
    sourceIdeal p x.firstCommon*sourceIdeal p x.second.divisor*sourceIdeal p x.second.overlap)
  simp only [supported_mul_iff]
  exact ⟨⟨⟨canonical_prime_product_supported p hp hg hc _ _,canonical_source_ideal_supported p hp hg hc _⟩,
    canonical_source_ideal_supported p hp hg hc _⟩,canonical_source_ideal_supported p hp hg hc _⟩

include hp hg hc in
theorem actual_cell_labels_supported {Jo Jn:ℕ}(S:Finset (MarkedSecondSource ι Jo Jn))(d:BlockIndex):
    ∀I∈actualCellLabels p S d,Supported I :=by
  intro I hI
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hI
  exact actual_second_label_supported p hp hg hc x

include hp hg hc in
theorem actual_cell_labels_admissible {Jo Jn:ℕ}(S:Finset (MarkedSecondSource ι Jo Jn))(d:BlockIndex):
    ∀I∈(actualCellLabels p S d).filter Squarefree,CanonicalQuadraticSieve.Admissible I :=by
  intro I hI
  obtain ⟨hm,hs⟩:=Finset.mem_filter.mp hI
  have hh:=actual_cell_labels_supported p hp hg hc S d I hm
  exact ⟨hh.1,hs,hh.2⟩

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepData -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_step_arithmetic (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap eps pi : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (heps : 0≤eps)
    (hwindow : Real.exp window≤Z^(4*eta))
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap)
    (hbudget : eps*(ell+exponent Z (k 4)/2+exponent Z l+Lcap+11*eta/2)≤pi) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ActualSecondSourceConditions p S ∧
    (∀x∈S,x.second.frequency≠0) ∧
    (∀x∈S,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta (index p x))) ∧
    (∀d∈keys p S,0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d) ∧
    (∀x∈S,
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
        ≤Z^(exponent Z (k 4)+eta) ∧
      primeProductNorm p x.firstCommon≤Z^(exponent Z (k 2)+eta) ∧
      (Ideal.absNorm x.quotient:ℝ)≤Z^(exponent Z l+eta) ∧
      Z^(exponent Z j-eta)≤
        ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤Z^(exponent Z j+eta) ∧
      primeProductNorm p x.firstDivisor≤Z^(exponent Z (k 3)+eta)) ∧
    (∀d,∀x∈cell p S d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p S d) ∧
    (∀d,∀I∈(actualCellLabels p S d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)) ∧
    (∀x∈S,∀i,outerNorms p x i≤Z^Lcap) ∧
    (∀x∈S,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*columnScale Z r k l negative) ∧
    (∀d∈keys p S,eps*(secondCount ell (exponent Z (k 4)) (exponent Z j) (exponent Z l)
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi) := by
  intro S
  have hr := source_row_gates p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hwindow
  have hl := source_labels p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hQ
  exact ⟨source_valid p hp pool Q k l j negative J lists Z M r ell V eta tau window b,
    source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b,
    hr.1,hr.2,
    retained_label_numeric p hp pool Q k l j Z ell eta hZ heta hbin hQ negative J lists _ b _,
    hl.1,hl.2,
    source_outer_caps p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap
      hZ hcol hYi hgeom hphysical,
    source_geometry p pool Q k l j negative J lists Z M r ell V eta tau window b,
    source_mass_gate p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap eps pi
      hZ heps hcol hYi hgeom hphysical hbudget⟩

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepPhysicalGates -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff InversePrioritySecondSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0)

def parentWeight (l : ℕ) (x : Source ι 0) : ℂ :=
  (‖commonSelector p (fun _=>1) l x.quotientSupport‖:ℂ)

lemma parentWeight_norm (l : ℕ) (x : Source ι 0) : ‖parentWeight p l x‖≤1 := by
  simp only [parentWeight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  simpa using InverseFirstGlobalCaps.commonSelector_norm p (fun _=>1) l x.quotientSupport

lemma secondCutoff_nonneg (Z M r ell V eta tau window : ℝ) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (hZ : 0<Z) (G E : Finset ι) :
    0≤ secondCutoff p Z M r ell V eta tau window k l j negative G E := by
  apply uniformSecondRadius_nonneg _ _ _ _ _ _ _ _ _ hZ.le
  · unfold firstCellRadius
    positivity
  · exact Real.rpow_nonneg hZ.le _

include hp in
theorem secondCutoff_dominates (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (Z M r ell V eta tau window : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,∀G E : Finset ι,
      correlatedSecondRadius p (secondParentDivisor p (parent p y)) G E
        (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j) (Z^tau)≤
      secondCutoff p Z M r ell V eta tau window k l j negative G E := by
  intro y hy G E
  have hd := (InverseFirstGlobalCaps.parentCell_ideal_bounds p hp pool Q (fun _ _=>1) k l
    Z eta hZ hbin y (Finset.mem_filter.mp hy).1).2.1.2
  apply correlated_le_uniform p Z (exponent Z (k 3)) eta _ G E _ _ _
    (by unfold firstCellRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  simpa [secondParentDivisor,parent,InverseFirstGlobalCaps.sourceIdeal_norm,
    primeSubsetGenerator_norm_eq_productNorm] using hd

include hp in
theorem parent_tail_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (Z ell eta Lcap : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hcap : 0≤Lcap)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hell : ell+eta≤Lcap) (hactive : exponent Z (k 4)+eta≤Lcap)
    (hcommon : exponent Z (k 2)+eta≤Lcap) (hquot : exponent Z l+eta≤Lcap) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^Lcap ∧
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^Lcap ∧
      ‖eisEmbedding (∏i∈cubeActiveSupport y.cube.support
        (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit,p i)‖≤Z^Lcap ∧
      primeProductNorm p y.firstCommon≤Z^Lcap ∧ primeProductNorm p y.quotientSupport≤Z^Lcap := by
  intro y hy
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ y hy
  have hpw {a : ℝ} (ha : a≤Lcap) : Z^a≤Z^Lcap := Real.rpow_le_rpow_of_exponent_le hZ.le ha
  refine ⟨hb.1.trans (hpw hell),hb.2.1.trans (hpw hell),?_,
    hb.2.2.2.1.trans (hpw hcommon),hb.2.2.2.2.1.trans (hpw hquot)⟩
  have he := hb.2.2.1.trans (hpw hactive)
  have hone := Real.one_le_rpow hZ.le hcap
  change ‖eisEmbedding (∏i∈_,p i)‖^2≤Z^Lcap at he
  have hn := norm_nonneg (eisEmbedding (∏i∈cubeActiveSupport y.cube.support
    (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit,p i))
  nlinarith

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI

end

