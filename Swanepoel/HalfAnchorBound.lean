module
public import Swanepoel.HalfSectorConstruction
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable
namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem half_sector_ports_no_crossings (ht : G.TriangleFree) (side : Bool) (v : TrackComponent G)
    (hmiss : ∀ e : OrientedEdge G, SpineSource e → G.sourceFace e∈B.bankDefectFamily ht side →
      ¬ComponentCrosses (edgeComponent e) v) :
    Nonempty (HalfSectorPorts G ht cut v (B.bankDefectFamily ht side) Bool) := by
  refine ⟨{
    subset_defects := Finset.filter_subset _ _
    code := fun _ => side
    direction := fun _ => -B.signedVector side
    direction_ne_zero := ?_
    missing := ?_
    same_code := by intros; rfl }⟩
  · intro code hz
    have hn := B.signedVector_norm side
    rw [neg_eq_zero.mp hz,norm_zero] at hn
    norm_num at hn
  · intro F hF e he hp
    have he' := (Finset.mem_filter.mp he).2
    have heY : G.sourceFace e∈B.bankDefectFamily ht side := he'.2 ▸ hF
    constructor
    · intro hU
      have hh := B.crossing_signed_normal_pos ht e he'.1 (Finset.mem_filter.mp heY).1
        ((componentGraph G ht).adj_symm hU)
      rw [(Finset.mem_filter.mp heY).2] at hh
      rw [inner_neg_left] at hp
      linarith
    · exact fun hV => hmiss e he'.1 heY ((componentGraph G ht).adj_symm hV)

theorem half_sector_ports (ht : G.TriangleFree) (hcut : cut∈G.ordinaryTrackComponents)
    (side : Bool) (v : TrackComponent G) (hUV : ComponentCrosses cut v)
    (hnot : v∉B.bankAnchorTracks ht side) :
    Nonempty (HalfSectorPorts G ht cut v (B.bankDefectFamily ht side) Bool) := by
  by_cases hactive : ∃ e : OrientedEdge G, SpineSource e ∧
      G.sourceFace e∈B.bankDefectFamily ht side ∧ ComponentCrosses (edgeComponent e) v
  · obtain ⟨e,he,heY,hCV⟩ := hactive
    have hneV : edgeComponent e≠v := (componentGraph G ht).ne_of_adj hCV
    obtain ⟨P⟩ := B.exists_nonanchor_halfCutPiece ht side v ((componentGraph G ht).adj_symm hUV) hnot
    have hnV : v≠cut := Ne.symm ((componentGraph G ht).ne_of_adj hUV)
    obtain ⟨q,hqc,hqcut,_⟩ := crossing_cut_transition_pair ht (edgeComponent e) v hneV hCV
    obtain ⟨C,hG,hH,_⟩ := q.property
    have hneQ : edgeComponent q.val.1≠v := fun h => hneV (hqc.symm.trans h)
    have hAD := q.other_component_eq_cut ht v hqcut hneQ C hG hH
    have hAB : edgeComponent C.edgeAB=edgeComponent e := by
      have heq : q.val.1=C.edgeAB := Subtype.ext hG
      rwa [← heq]
    obtain ⟨a,b,hab,ha,_,hcorners⟩ := C.spineWitness ht v (Or.inr hAD)
    have hac : a.val.1∈C.corners := by rw [← hcorners]; simp [stepCorners]
    have hbc : b.val.1∈C.corners := by rw [← hcorners]; simp [stepCorners]
    have hb : edgeComponent b=v := (positive_path_component (Relation.ReflTransGen.single hab)).symm.trans ha
    have ham := P.anchor_crossing_midpoint_mem hcut hUV e he heY C hAB hAD a ha hac
    have hbm := P.anchor_crossing_midpoint_mem hcut hUV e he heY C hAB hAD b hb hbc
    have hnt := P.nontrivial_of_step_midpoints hab ha ham hbm
    obtain ⟨V⟩ := P.exists_local_bank_data hcut hnV hnt
    exact V.sector_ports hcut hUV hnot
  · apply B.half_sector_ports_no_crossings ht side v
    intro e he heY hCV
    exact hactive ⟨e,he,heY,hCV⟩

theorem nonAnchor_bound (ht : G.TriangleFree)
    (hdegree : ∀ a b, G.graph.Adj a b → ∃ c, G.graph.Adj a c ∧ c≠b)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) (v : TrackComponent G)
    (hUV : ComponentCrosses cut v) (hnot : v∉B.bankAnchorTracks ht side) :
    (((B.bankAnchorTracks ht side).filter (ComponentCrosses v)).card : ℤ)≤
      B.bankK ht side-(B.bankMeetingAnchors ht side).card := by
  obtain ⟨D⟩ := B.half_sector_ports ht hcut side v hUV hnot
  have hh := D.anchor_count hdegree hUV
  change (((B.bankAnchorTracks ht side).filter (ComponentCrosses v)).card : ℤ)≤
    (B.bankAnchorTracks ht side).card-(B.bankMeetingAnchors ht side).card-
      2*(B.bankDefectFamily ht side).card at hh
  unfold bankK
  omega

end OrdinaryCutBanks
end Swanepoel
