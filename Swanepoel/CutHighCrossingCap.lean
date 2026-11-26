module
public import Swanepoel.CutHalfAccounting
public import Swanepoel.DisjointReduction
public import Swanepoel.CutNonAnchorSelection
public import Swanepoel.CutCanonicalList
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable
namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem canonical_half_cap_of_high_bank (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (hhigh : 39*(B.canonicalHalfSystem ht side).k≤100*(B.canonicalHalfSystem ht side).d) :
    (B.canonicalHalfSystem ht side).R+(B.inheritedNonAnchorCrossings ht side : ℤ)≤
      ((B.canonicalHalfSystem ht side).d+(B.inheritedNonAnchors ht side).card)*
        ((B.canonicalHalfSystem ht side).k-(B.canonicalHalfSystem ht side).d) := by
  have hR := B.canonicalHalfSystem_lemma_3_8 ht hc hdegree hcut side hhigh
  have ho := B.inheritedNonAnchorCrossings_le ht hc hdegree hcut side
  calc
    _≤(B.canonicalHalfSystem ht side).d*
        ((B.canonicalHalfSystem ht side).k-(B.canonicalHalfSystem ht side).d)+
        (B.inheritedNonAnchors ht side).card*
        ((B.canonicalHalfSystem ht side).k-(B.canonicalHalfSystem ht side).d) := add_le_add hR ho
    _=_ := by ring

theorem canonical_cut_cap_from_half_caps (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents)
    (hcap : ∀ side : Bool,
      (B.canonicalHalfSystem ht side).R+(B.inheritedNonAnchorCrossings ht side : ℤ)≤
        ((B.canonicalHalfSystem ht side).d+(B.inheritedNonAnchors ht side).card)*
          ((B.canonicalHalfSystem ht side).k-(B.canonicalHalfSystem ht side).d)) :
    ((componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).r : ℤ)+G.faceDefectCount ht≤
      (B.terminalCutCrossers.card : ℤ)*
        ((componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K-B.terminalCutCrossers.card) := by
  have h := B.canonical_cut_conservation ht hc hcut
  have ho (side : Bool) : (B.canonicalHalfSystem ht side).d+
      (B.inheritedNonAnchors ht side).card=(B.terminalCutCrossers.card : ℤ) := by
    have hh := h.2.2 side
    rw [B.canonicalInheritedNonAnchors_card ht hc hcut side] at hh
    exact hh
  have hp := cut_product_identity
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K
    B.terminalCutCrossers.card (B.splitTerminalJoins ht).card
    (B.canonicalHalfSystem ht false).k (B.canonicalHalfSystem ht true).k
    (B.canonicalHalfSystem ht false).d (B.canonicalHalfSystem ht true).d
    (B.inheritedNonAnchors ht false).card (B.inheritedNonAnchors ht true).card
    h.1 h.2.1 (ho false) (ho true)
  have ha := B.canonical_cut_R_allocation ht hc hcut
  calc
    _=((B.canonicalHalfSystem ht false).R+(B.inheritedNonAnchorCrossings ht false : ℤ))+
        ((B.canonicalHalfSystem ht true).R+(B.inheritedNonAnchorCrossings ht true : ℤ)) := by
      linarith only [ha]
    _≤_ := add_le_add (hcap false) (hcap true)
    _=_ := hp

theorem canonical_cut_cap_of_half_disjoint_bounds (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents)
    (hglobal : 61*(componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K<
      100*(B.terminalCutCrossers.card : ℤ))
    (hrec : ∀ side : Bool,(B.canonicalHalfTracks ht side).DisjointBound) :
    ((componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).r : ℤ)+G.faceDefectCount ht≤
      (B.terminalCutCrossers.card : ℤ)*
        ((componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K-B.terminalCutCrossers.card) := by
  apply B.canonical_cut_cap_from_half_caps ht hc hcut
  intro side
  by_cases hh : 39*(B.canonicalHalfSystem ht side).k≤100*(B.canonicalHalfSystem ht side).d
  · exact B.canonical_half_cap_of_high_bank ht hc hdegree hcut side hh
  · exact B.canonical_small_bank_cap ht hc hdegree hcut side hglobal (by omega) (hrec side)

end OrdinaryCutBanks

theorem PennyGraph.high_crossing_cap_of_smaller_connected_bounds
    {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (ih : ∀ m<n,∀ H : PennyGraph m,∀ hH : H.TriangleFree,H.graph.Connected →
      (componentSystem H hH H.ordinaryTrackComponents (H.faceDefectCount hH)).DisjointBound) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).HighCrossingCap := by
  let D := componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)
  let E := Fintype.equivFin (TrackComponent G)
  change ∀ u : Fin (Fintype.card (TrackComponent G)),u∈D.ordinary →
    61*D.K<100*(D.s u : ℤ) →
      (D.r : ℤ)+D.defects≤(D.s u : ℤ)*(D.K-D.s u)
  intro u hu hhigh
  let cut : TrackComponent G := E.symm u
  have hcut : cut∈G.ordinaryTrackComponents := by
    change u∈G.ordinaryTrackComponents.map E.toEmbedding at hu
    exact Finset.mem_map_equiv.mp hu
  have hK := G.canonical_componentSystem_K_nonneg ht
  have hspos : 0<D.s u := by
    change 61*D.K<100*(D.s u : ℤ) at hhigh
    change 0≤D.K at hK
    omega
  change 0<(D.terminal.filter (D.crossing.Adj u)).card at hspos
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hspos
  have huv := (Finset.mem_filter.mp hv).2
  have hcross : ComponentCrosses cut (E.symm v) := huv
  obtain ⟨B⟩ := exists_ordinaryCutBanks ht cut (E.symm v) hcut hcross
  have hs := B.terminalCutCrossers_card_eq_s ht
  change B.terminalCutCrossers.card=D.s (E (E.symm u)) at hs
  rw [E.apply_symm_apply] at hs
  have hglobal : 61*D.K<100*(B.terminalCutCrossers.card : ℤ) := by
    rw [hs]
    exact hhigh
  have hrec (side : Bool) : (B.canonicalHalfTracks ht side).DisjointBound :=
    ih _ (B.half_vertex_count_lt ht side) (B.halfGraph side)
      (B.halfGraph_triangleFree ht side) (B.halfGraph_connected ht hc side)
  have hcap := B.canonical_cut_cap_of_half_disjoint_bounds ht hc hdegree hcut hglobal hrec
  rw [hs] at hcap
  exact hcap

theorem PennyGraph.disjoint_bound_of_min_degree_and_smaller_bounds
    {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (ih : ∀ m<n,∀ H : PennyGraph m,∀ hH : H.TriangleFree,H.graph.Connected →
      (componentSystem H hH H.ordinaryTrackComponents (H.faceDefectCount hH)).DisjointBound) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).DisjointBound :=
  G.canonical_disjoint_bound_of_high_crossing_cap ht (G.lemma_3_7 ht hc hdegree)
    (G.high_crossing_cap_of_smaller_connected_bounds ht hc hdegree ih)

end Swanepoel
