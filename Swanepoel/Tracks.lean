module
public import Swanepoel.Arithmetic
@[expose] public section

noncomputable section
namespace Swanepoel

structure TrackSystem where
  count : ℕ
  ordinary : Finset (Fin count)
  crossing : SimpleGraph (Fin count)
  defects : ℕ

namespace TrackSystem
variable (D : TrackSystem)

abbrev Track := Fin D.count
def terminal : Finset D.Track := Finset.univ \ D.ordinary
def p : ℕ := D.terminal.card
def t : ℕ := D.ordinary.card
def K : ℤ := (D.p : ℤ) - 2 * D.defects

def crossings (A B : Finset D.Track) : ℕ := by
  classical
  exact ((A.product B).filter fun uv => D.crossing.Adj uv.1 uv.2).card

def internal (A : Finset D.Track) : ℕ := by
  classical
  exact ((A.product A).filter fun uv => uv.1 < uv.2 ∧ D.crossing.Adj uv.1 uv.2).card

def r : ℕ := D.internal D.terminal
def q : ℕ := D.internal Finset.univ
def s (u : D.Track) : ℕ := by
  classical
  exact (D.terminal.filter (D.crossing.Adj u)).card

def Disjoint (A : Finset D.Track) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, ¬ D.crossing.Adj u v

def Q (A : Finset D.Track) : ℤ :=
  D.r + (∑ u ∈ A, (D.s u : ℤ)) + D.internal A

def NoTriple : Prop :=
  ∀ u v w, D.crossing.Adj u v → D.crossing.Adj v w → ¬ D.crossing.Adj w u

def CrossingPairBound : Prop :=
  ∀ u ∈ D.ordinary, ∀ v ∈ D.ordinary, D.crossing.Adj u v →
    (D.s u : ℤ) + D.s v ≤ D.K

def DisjointBound : Prop :=
  ∀ A ⊆ D.ordinary, D.Disjoint A →
    (D.r : ℤ) + D.defects + (∑ u ∈ A, (D.s u : ℤ)) ≤ N (D.K + A.card)

def QuadraticBound : Prop :=
  10000 * ((D.r : ℤ) + D.defects) ≤ 2379 * D.K ^ 2

end TrackSystem

structure HalfSystem where
  tracks : TrackSystem
  bankAnchors : Finset tracks.Track
  bank_terminal : bankAnchors ⊆ tracks.terminal
  nonAnchorCrossers : Finset tracks.Track
  nonAnchor_ordinary : nonAnchorCrossers ⊆ tracks.ordinary

namespace HalfSystem
def d (H : HalfSystem) : ℤ := H.bankAnchors.card
def k (H : HalfSystem) : ℤ := H.tracks.K
def R (H : HalfSystem) : ℤ := (H.tracks.r : ℤ) + H.tracks.defects

def NonAnchorBound (H : HalfSystem) : Prop :=
  ∀ u ∈ H.nonAnchorCrossers, (H.tracks.s u : ℤ) ≤ H.k - H.d

def BankBound (H : HalfSystem) : Prop := 10 * H.d ≤ 9 * H.k

def HighBankBound (H : HalfSystem) : Prop :=
  39 * H.k ≤ 100 * H.d → H.R ≤ H.d * (H.k - H.d)
end HalfSystem

end Swanepoel
