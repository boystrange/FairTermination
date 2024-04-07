-- This file is part of FairTermination

-- FairTermination is free software: you can redistribute it and/or
-- modify it under the terms of the GNU General Public License as
-- published by the Free Software Foundation, either version 3 of
-- the License, or (at your option) any later version.

-- FairTermination is distributed in the hope that it will be
-- useful, but WITHOUT ANY WARRANTY; without even the implied
-- warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
-- See the GNU General Public License for more details.

-- You should have received a copy of the GNU General Public License
-- along with FairTermination. If not, see
-- <http://www.gnu.org/licenses/>.

-- Copyright 2022 Luca Padovani

{-# OPTIONS --guardedness #-}

module FairTermination (State : Set) (_~>_ : State -> State -> Set) where

import Level using (zero)
open import Axiom.ExcludedMiddle using (ExcludedMiddle)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Satisfiable; _∪_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Function.Base using (_∘_)

postulate excluded-middle : ExcludedMiddle Level.zero

StateProp : Set₁
StateProp = State -> Set

-- Reflexive and transitive closure of the reduction relation.

_~>*_ : Rel State _
_~>*_ = Star _~>_

-- A state S reduces if S ~> S' for some S' and it is stuck if it
-- does not reduce.

Reduces : StateProp
Reduces S = Satisfiable (S ~>_)

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

make-any-run : (S : State) -> ∞Run S
make-any-run S with excluded-middle {Reduces S}
... | yes (S' , red) = λ where .force -> red :: make-any-run S'
... | no stuck = λ where .force -> stop stuck

_++_ : ∀{S S'} -> S ~>* S' -> Run S' -> Run S
ε ++ ρ = ρ
(red ◅ reds) ++ ρ = red :: (λ where .force -> reds ++ ρ)

RunProp : Set₁
RunProp = ∀{S} -> Run S -> Set

-- Each property P of states induces a corresponding property of
-- runs in which there is a state that satisfies P.

data Eventually (P : StateProp) : RunProp where
  here : ∀{S} {ρ : Run S} (proof : P S) -> Eventually P ρ
  next : ∀{S S'} (red : S ~> S') {ρ : ∞Run S'} (ev : Eventually P (ρ .force)) -> Eventually P (red :: ρ)

++-eventually : (P : StateProp) -> ∀{S S'} (reds : S ~>* S') {ρ : Run S'} -> Eventually P ρ -> Eventually P (reds ++ ρ)
++-eventually P ε ev = ev
++-eventually P (red ◅ reds) ev = next red (++-eventually P reds ev)

eventually-imp : (P Q : StateProp) -> (∀{S} -> P S -> Q S) -> ∀{S} {ρ : Run S} -> Eventually P ρ -> Eventually Q ρ
eventually-imp _ _ imp (here proof) = here (imp proof)
eventually-imp P Q imp (next red ev) = next red (eventually-imp P Q imp ev)

-- A run is finite if it contains a stuck state.

Finite : RunProp
Finite = Eventually Stuck

finite-++ : ∀{S S'} (reds : S ~>* S') {ρ : Run S'} -> Finite (reds ++ ρ) -> Finite ρ
finite-++ ε fin = fin
finite-++ (red ◅ reds) (here stuck) = ⊥-elim (stuck (_ , red))
finite-++ (red ◅ reds) (next _ fin) = finite-++ reds fin

-- A state is weakly terminating if it has a finite run. A state is
-- non terminating if it is not weakly terminating.

WeaklyTerminating : StateProp
WeaklyTerminating S = Σ[ ρ ∈ Run S ] Finite ρ

NonTerminating : StateProp
NonTerminating S = ¬ WeaklyTerminating S

-- A fairness assumption is a proposition over runs such that every
-- partial run S ~>* S' can be extended to a fair run. This
-- condition is called feasibility or machine closure

record FairnessAssumption : Set₁ where
  field
    Fair : RunProp
    feasible : ∀{S S'} (reds : S ~>* S') -> Σ[ ρ ∈ Run S' ] Fair (reds ++ ρ)
open FairnessAssumption public

-- A run is fair if it contains finitely many weakly terminating
-- states. This means that the run is either finite or divergent.

FullFairness : FairnessAssumption
FullFairness = record { Fair = Fair' ; feasible = feasible' }
  where
    Fair' : RunProp
    Fair' = Eventually (Stuck ∪ NonTerminating)

    make : (S : State) -> Σ[ ρ ∈ Run S ] Fair' ρ
    make S with excluded-middle {WeaklyTerminating S}
    ... | yes (_ , fin) = _ , eventually-imp Stuck (Stuck ∪ NonTerminating) inj₁ fin
    ... | no nt = make-any-run S .force , here (inj₂ nt)

    feasible' : ∀{S S'} (reds : S ~>* S') -> Σ[ ρ ∈ Run S' ] Fair' (reds ++ ρ)
    feasible' {_} {S'} reds = let _ , fair = make S' in _ , ++-eventually _ reds fair

-- A state S is fairly terminating if the fair runs of S are finite.

FairlyTerminating : FairnessAssumption -> StateProp
FairlyTerminating ϕ S = ∀{ρ : Run S} -> Fair ϕ ρ -> Finite ρ

-- Here is the alternative characterization of fair termination that
-- does not use fair runs. A state S satisfies the specification if
-- any S' that is reachable from S is weakly terminating.

Specification : StateProp
Specification S = ∀{S'} -> S ~>* S' -> WeaklyTerminating S'

-- The specification is a *necessary* condition for fair
-- termination, regardless of the fairness assumption being made

ft->spec : (ϕ : FairnessAssumption) -> ∀{S} -> FairlyTerminating ϕ S -> Specification S
ft->spec ϕ ft {S'} reds = let _ , fair = feasible ϕ reds in
                          _ , finite-++ reds (ft fair)

-- The specification is a *sufficient* condition for the notion of
-- fair termination induced by FullFairness

spec->ft : ∀{S} -> Specification S -> FairlyTerminating FullFairness S
spec->ft spec (here (inj₁ stuck)) = here stuck
spec->ft spec (here (inj₂ nt)) = ⊥-elim (nt (spec ε))
spec->ft spec (next red fair) = next red (spec->ft (λ reds -> spec (red ◅ reds)) fair)

-- As a consequence, FullFairness is the fairness assumption that
-- induces the largest family of fairly terminating states

ft->ft : (ϕ : FairnessAssumption) -> ∀{S} -> FairlyTerminating ϕ S -> FairlyTerminating FullFairness S
ft->ft ϕ = spec->ft ∘ ft->spec ϕ
