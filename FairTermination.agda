{-# OPTIONS --guardedness #-}

module FairTermination (State : Set) (_~>_ : State -> State -> Set) where

import Level using (zero)
open import Axiom.ExcludedMiddle using (ExcludedMiddle)
open import Axiom.DoubleNegationElimination using (DoubleNegationElimination)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Empty; Satisfiable; _∪_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Function.Base using (_∘_)

postulate
  excluded-middle : ExcludedMiddle Level.zero
  double-negation-elimination : DoubleNegationElimination Level.zero

StateProp : Set₁
StateProp = State -> Set

-- Reflexive and transitive closure of the reduction relation.

_~>*_ : Rel State _
_~>*_ = Star _~>_

-- A state S reduces if S ~> S' for some S'.

Reduces : StateProp
Reduces S = Satisfiable (S ~>_)

-- A state is stuck if it does not reduce.

Stuck : StateProp
Stuck S = ¬ (Reduces S)

-- A run is a maximal sequence S ~> S₁ ~> S₂ ~> ..., that is a
-- sequence of reductions that is either infinite or it ends with a
-- stuck state Sₙ.

data Run (S : State) : Set
record ∞Run (S : State) : Set where
  coinductive
  field force : Run S
open ∞Run public

data Run S where
  stop : (stuck : Stuck S) -> Run S
  _::_ : ∀{S'} (red : S ~> S') (ρ : ∞Run S') -> Run S

RunProp : Set₁
RunProp = ∀{S} -> Run S -> Set

-- We say that S belongs to ρ, notation S ∈ ρ, if S occurs somewhere
-- in ρ.

data _∈_ : State -> RunProp where
  here : ∀{S} (ρ : Run S) -> S ∈ ρ
  step : ∀{S S' T} (red : S ~> S') (ρ : ∞Run S') (pin : T ∈ ρ .force) -> T ∈ (red :: ρ)

-- We can build run propositions from state propositions using the
-- "eventually" and "always" modalities.

Eventually : StateProp -> RunProp
Eventually P ρ = ∃[ S ] S ∈ ρ × P S

Always : StateProp -> RunProp
Always P ρ = ∀{S} -> S ∈ ρ -> P S

-- If a state property P does not eventually hold in some run ρ,
-- then the negation of P always holds in ρ.

¬Eventually->Always¬ : (P : StateProp) -> ∀{S} {ρ : Run S} -> ¬ Eventually P ρ -> Always (¬_ ∘ P) ρ
¬Eventually->Always¬ P {S} nep {T} pin with excluded-middle {P T}
... | yes p = ⊥-elim (nep (_ , pin , p))
... | no np = np

-- A run is finite if it contains a stuck state. Conversely, a run
-- is infinite if each of its states reduces.

Finite : RunProp
Finite = Eventually Stuck

Infinite : RunProp
Infinite = Always Reduces

-- We prove that Finite and Infinite are one the negation of the
-- other.

finite->¬infinite : ∀{S} {ρ : Run S} -> Finite ρ -> ¬ Infinite ρ
finite->¬infinite (_ , pin , stuck) inf = stuck (inf pin)

¬finite->infinite : ∀{S} {ρ : Run S} -> ¬ Finite ρ -> Infinite ρ
¬finite->infinite nfin pin = double-negation-elimination (¬Eventually->Always¬ Stuck nfin pin)

-- A state S is weakly terminating if there is a finite run of S.

WeaklyTerminating : StateProp
WeaklyTerminating S = Σ[ ρ ∈ Run S ] Finite ρ

-- A state S is non terminating if any run of S is infinite.

NonTerminating : StateProp
NonTerminating S = (ρ : Run S) -> Infinite ρ

-- We prove that weak termination and non termination are one the
-- opposite of the other.

wt->¬nt : ∀{S} -> WeaklyTerminating S -> ¬ NonTerminating S
wt->¬nt (ρ , fin) nt = finite->¬infinite fin (nt ρ)

¬wt->nt : ∀{S} -> ¬ WeaklyTerminating S -> NonTerminating S
¬wt->nt nwt ρ pin with excluded-middle {Finite ρ}
... | yes fin = ⊥-elim (nwt (ρ , fin))
... | no nfin = ¬finite->infinite nfin pin

-- A run is fair if it contains finitely many weakly terminating
-- states. This means that either the run is finite, or it
-- eventually contains a non-terminating state.

Fair : RunProp
Fair = Eventually Stuck ∪ Eventually NonTerminating

-- A state S is fairly terminating if all the fair runs of S are
-- finite.

FairlyTerminating : StateProp
FairlyTerminating S = (ρ : Run S) (fair : Fair ρ) -> Finite ρ

-- Here is the alternative characterization of fair termination that
-- does not use fair runs. A state S satisfies the specification if
-- any S' that is reachable from S is weakly terminating.

Specification : StateProp
Specification S = ∀{S'} -> S ~>* S' -> WeaklyTerminating S'

-- Any state has an arbitrary and a fair run.

make-run : (S : State) -> ∞Run S
make-run S with excluded-middle {Reduces S}
... | yes (S' , red) = λ where .force -> red :: make-run S'
... | no stuck = λ where .force -> stop stuck

make-fair-run : (S : State) -> Σ[ ρ ∈ Run S ] Fair ρ
make-fair-run S with excluded-middle {WeaklyTerminating S}
... | yes (ρ , fin) = ρ , inj₁ fin
... | no nwt with make-run S .force
... | ρ = ρ , inj₂ (S , here ρ , ¬wt->nt nwt)

-- Eventual stuckness, eventual non termination and fairness are
-- preserved by ::

::-eventually : (P : StateProp) -> ∀{S S'} (red : S ~> S') {ρ : ∞Run S'} -> Eventually P (ρ .force) -> Eventually P (red :: ρ)
::-eventually P {S} {S'} red {ρ} (T , pin , p) = T , step red ρ pin , p

::-eventually-stuck : ∀{S S'} (red : S ~> S') {ρ : ∞Run S'} -> Eventually Stuck (ρ .force) -> Eventually Stuck (red :: ρ)
::-eventually-stuck = ::-eventually Stuck

::-eventually-nt : ∀{S S'} (red : S ~> S') {ρ : ∞Run S'} -> Eventually NonTerminating (ρ .force) -> Eventually NonTerminating (red :: ρ)
::-eventually-nt = ::-eventually NonTerminating

::-fair : ∀{S S'} {ρ : ∞Run S'} (red : S ~> S') -> Fair (ρ .force) -> Fair (red :: ρ)
::-fair red (inj₁ fin) = inj₁ (::-eventually-stuck red fin)
::-fair red (inj₂ ent) = inj₂ (::-eventually-nt red ent)

-- Some auxiliary results concerning ∈

∈-stuck : ∀{S S' T} {red : S ~> S'} {ρ : ∞Run S'} -> Stuck T -> T ∈ (red :: ρ) -> T ∈ ρ .force
∈-stuck {_} {_} {_} {red} stuck (here .(_ :: _)) = ⊥-elim (stuck (_ , red))
∈-stuck _ (step _ _ pin) = pin

∈-reductions : ∀{S S'} {ρ : Run S} -> S' ∈ ρ -> S ~>* S'
∈-reductions (here _) = ε
∈-reductions (step red _ pin) = red ◅ ∈-reductions pin

-- Fair termination is preserved by reductions.

~>-ft : ∀{S S'} -> S ~> S' -> FairlyTerminating S -> FairlyTerminating S'
~>-ft red ft ρ fair with ft (red :: λ where .force -> ρ) (::-fair red fair)
... | T , pin , stuck = T , ∈-stuck stuck pin , stuck

~>*-ft : ∀{S S'} -> S ~>* S' -> FairlyTerminating S -> FairlyTerminating S'
~>*-ft ε ft = ft
~>*-ft (red ◅ reds) ft = ~>*-ft reds (~>-ft red ft)

-- Fair termination implies weak termination.

ft->wt : ∀{S} -> FairlyTerminating S -> WeaklyTerminating S
ft->wt {S} ft with make-fair-run S
... | ρ , fair with ft ρ fair
... | fin = ρ , fin

-- Alternative characterization of fair termination.

ft->spec : ∀{S} -> FairlyTerminating S -> Specification S
ft->spec ft reds = ft->wt (~>*-ft reds ft)

spec->ft : ∀{S} -> Specification S -> FairlyTerminating S
spec->ft spec ρ (inj₁ fin) = fin
spec->ft spec ρ (inj₂ (T , pin , nt)) with spec (∈-reductions pin)
... | wt = ⊥-elim (wt->¬nt wt nt)
