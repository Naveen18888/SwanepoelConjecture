module
public import Swanepoel.HalfAnchorLocation
public import Swanepoel.TwoSpineSources
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

theorem MaskedSpineChain.exists_half_local_banks_of_ne {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)
    (hcut : cut∈G.ordinaryTrackComponents) {s g h finish : OrientedEdge G}
    (p : MaskedSpineChain G cut s g) (hs : SpineSource s)
    (hext : ¬Bornology.IsBounded (G.sourceFace s).val)
    (htop : ¬∃a,PositiveCellStep finish a)
    (hfull : Relation.ReflTransGen PositiveCellStep s finish)
    (hne : edgeComponent s≠cut) (hnt : s≠g) (C : RhombusCell G)
    (hG : g.val=(C.a,C.b)) (hH : h.val=(C.d,C.c)) (hpos : 0<cross2 C.u C.v)
    (hAD : edgeComponent C.edgeAD=cut) :
    ∃ loop : PlaneChain (edgeCenter s) (edgeCenter s),
      loop.trace⊆(trackSpineTrace (edgeComponent s)∪trackSpineTrace cut)∪B.outer.val ∧
      (∀ sign : ℝ, sign=1 ∨ sign= -1 → Disjoint (p.positive.bankRegion sign) loop.trace) ∧
      p.positive.bankLabel loop (-1)=p.positive.bankLabel loop 1+1 := by
  cases p with
  | nil => exact False.elim (hnt rfl)
  | cons s b g hsb tail =>
    obtain ⟨loop,_,hloop,hdis,hdiff⟩ := tail.exists_half_local_banks ht B hcut hsb hs
      hext htop hfull hne C hG hH hpos hAD
    exact ⟨loop,hloop,hdis,hdiff⟩

structure HalfLocalBankData {n : ℕ} {G : PennyGraph n} {cut v : TrackComponent G}
    {B : OrdinaryCutBanks G cut} {ht : G.TriangleFree} {side : Bool}
    (P : HalfCutPiece B ht side v) where
  loop : PlaneChain (edgeCenter P.start) (edgeCenter P.start)
  support : loop.trace⊆(trackSpineTrace cut∪trackSpineTrace v)∪B.outer.val
  bank_disjoint : ∀ sign : ℝ, sign=1 ∨ sign= -1 → Disjoint (P.chain.positive.bankRegion sign) loop.trace
  difference : P.chain.positive.bankLabel loop (-1)=P.chain.positive.bankLabel loop 1+1

theorem HalfCutPiece.exists_local_bank_data {n : ℕ} {G : PennyGraph n} {cut v : TrackComponent G}
    {B : OrdinaryCutBanks G cut} {ht : G.TriangleFree} {side : Bool}
    (P : HalfCutPiece B ht side v) (hcut : cut∈G.ordinaryTrackComponents)
    (hne : v≠cut) (hnt : P.start≠P.crossing.val.1) : Nonempty (HalfLocalBankData P) := by
  obtain ⟨C,hG,hH,hpos⟩ := P.crossing.property
  have hns : edgeComponent P.start≠cut := fun h => hne (P.component.symm.trans h)
  have hng : edgeComponent P.crossing.val.1≠cut := by
    rwa [← positive_path_component P.before]
  have hAD := P.crossing.other_component_eq_cut ht cut P.removed hng C hG hH
  obtain ⟨loop,hsupport,hdis,hdiff⟩ := P.chain.exists_half_local_banks_of_ne ht B hcut P.source
    P.exterior P.sink P.full_reach hns hnt C hG hH hpos hAD
  exact ⟨⟨loop,by simpa only [P.component,union_comm] using hsupport,hdis,hdiff⟩⟩

namespace HalfLocalBankData
variable {n : ℕ} {G : PennyGraph n} {cut v : TrackComponent G}
    {B : OrdinaryCutBanks G cut} {ht : G.TriangleFree} {side : Bool}
    {P : HalfCutPiece B ht side v} (V : HalfLocalBankData P)

def vector (_V : HalfLocalBankData P) : Plane := carriedVector P.start
def positiveLabel : ℤ := P.chain.positive.bankLabel V.loop 1
def negativeLabel : ℤ := P.chain.positive.bankLabel V.loop (-1)
def faceLabel (F : PlaneFace G) : ℤ := G.faceWindingLabel V.loop F
def bankCode (F : PlaneFace G) : Bool := decide (V.faceLabel F=V.positiveLabel)
def signedVector (code : Bool) : Plane := if code then V.vector else -V.vector

theorem labels_ne : V.positiveLabel≠V.negativeLabel := by
  have hh := V.difference
  change V.negativeLabel=V.positiveLabel+1 at hh
  omega

theorem signedVector_norm (code : Bool) : ‖V.signedVector code‖=1 := by
  cases code <;> simp [signedVector,vector,carriedVector_norm]

theorem signedVector_sameLine (code : Bool) : SameLine (V.signedVector code) (componentVector v) := by
  have hv := component_sameLine P.start v P.component
  cases code
  · exact (show SameLine (-V.vector) V.vector from Or.inr rfl).trans hv
  · exact hv

theorem crossing_source_label (hcut : cut∈G.ordinaryTrackComponents)
    (hUV : ComponentCrosses cut v) (e : OrientedEdge G) (he : SpineSource e)
    (heY : G.sourceFace e∈B.bankDefectFamily ht side)
    (hcross : ComponentCrosses (edgeComponent e) v) :
    (0 < inner ℝ V.vector (sourceNormal e) ∧ V.faceLabel (G.sourceFace e)=V.positiveLabel) ∨
      (inner ℝ V.vector (sourceNormal e)<0 ∧ V.faceLabel (G.sourceFace e)=V.negativeLabel) := by
  have hne : edgeComponent e≠v := (componentGraph G ht).ne_of_adj hcross
  have hnU := defect_source_component_ne_ordinary ht e he (Finset.mem_filter.mp heY).1 cut hcut
  have hmissU : ¬ComponentCrosses (edgeComponent e) cut := by
    intro h
    exact componentGraph_noTriple G ht cut v (edgeComponent e) hUV
      ((componentGraph G ht).adj_symm hcross) h
  obtain ⟨q,hqcut,hprefix,hpairs⟩ := crossing_cut_transition_before_source ht v e he hne hcross
  have hpath := path_before_global_cut_preserved v q hpairs hprefix
  have hlabels := two_spine_masked_path_winding_eq ht cut v B.outer V.loop V.support hpath hnU hmissU
  obtain ⟨C,hE,hF,hpos⟩ := q.property
  have hqne : edgeComponent q.val.1≠v := by rwa [← positive_path_component hprefix]
  have hAD := q.other_component_eq_cut ht v hqcut hqne C hE hF
  have hAB : edgeComponent C.edgeAB=edgeComponent e := by
    have heq : q.val.1=C.edgeAB := Subtype.ext hE
    rw [← heq]
    exact (positive_path_component hprefix).symm
  have hm := P.anchor_crossing_midpoint_mem hcut hUV e he heY C hAB hAD C.edgeAD hAD
    (by simp [RhombusCell.edgeAD,RhombusCell.corners])
  have hvector : carriedVector e=C.u := by
    rw [positive_path_vector_eq hprefix]
    simp only [carriedVector,hE,RhombusCell.u]
  have hdot : inner ℝ V.vector (sourceNormal e)=cross2 V.vector C.u := by
    rw [sourceNormal_inner_eq_cross,hvector]
  have hswap : cross2 C.v C.u= -cross2 C.u C.v := by unfold cross2; ring
  have hflabel : V.faceLabel (G.sourceFace e)=V.loop.windingIndex (G.point C.a) := by
    rw [faceLabel,← G.defect_vertex_two_spine_label ht cut v B.outer B.outer_unbounded V.loop V.support
      _ (Finset.mem_filter.mp heY).1 _ (G.sourceFace_endpoints_mem_closure e).1]
    simpa only [hE] using hlabels
  have hline := generated_track_sameLine (Quotient.exact (hAD.trans P.component.symm))
  rcases hline with hv | hv
  · change C.v=V.vector at hv
    right
    refine ⟨?_,?_⟩
    · rw [hdot,← hv,hswap]
      linarith
    · rw [hflabel]
      exact P.chain.positive.carried_start_label_of_mem V.loop (-1)
        (V.bank_disjoint (-1) (Or.inr rfl)) C.edgeAD hm (by
          change C.v=(-(-1:ℝ)) • V.vector
          simpa only [neg_neg,one_smul] using hv)
  · change C.v= -V.vector at hv
    have hneg : V.vector= -C.v := by rw [hv,neg_neg]
    left
    refine ⟨?_,?_⟩
    · rw [hdot,hneg,cross2_neg_left,hswap]
      linarith
    · rw [hflabel]
      exact P.chain.positive.carried_start_label_of_mem V.loop 1
        (V.bank_disjoint 1 (Or.inl rfl)) C.edgeAD hm (by
          change C.v=(-1:ℝ) • V.vector
          simpa only [neg_one_smul] using hv)

end HalfLocalBankData
end Swanepoel
