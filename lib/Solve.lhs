\subsection{Solving Tableaux}

The solve function is the function that we use to determine theoremhood of a formula. Since the rules for the implication-free fragments of intuitionistic logic and classical logic coincide, it can be used for determining theoremhood of formulas in any of the two systems.\\

\begin{code}
{-# LANGUAGE BlockArguments #-}

module Solve where

import Data.List

import Formulas
import Tableau
import Step
import HelperFunctions


\end{code}

First, we need to define some straightforward helper functions\\

\begin{code}
expanded :: Node -> Bool                             
expanded (Nd _ _ _ _ [] [] [])  = True
expanded  _                                = False

badNode :: Node -> Bool                             
badNode (Nd _ _ _ _ [] x _) | not(null x) = True              
                            | otherwise   = False
badNode _                                 = False

badTab :: Tableau -> Bool                            
badTab = any badNode

firstbad :: Tableau -> Node                          
firstbad [] = undefined
firstbad (n : ns)
  | not (badTab (n:ns)) = undefined
  | badNode n = n
  | otherwise = firstbad ns

removebad :: Tableau -> Tableau                      
removebad tab | badTab tab = tab \\ [firstbad tab]
              | otherwise = tab

\end{code}

Next is the function expand, which roughly corresponds to a \say{one step expansion} of a given tableau, and is given by \\

\begin{code}
expand :: Tableau -> [Tableau]                                  
expand tab | not (badTab tab) = [concatMap (head . step) tab]
           | otherwise = [ head (step (firstbad tab)) ++ removebad tab, last (step (firstbad tab)) ++ removebad tab ]

\end{code}

where a tableau is considered \say{bad} if it has at least one \say{bad} node, i.e. a node which has empty (i) and nonempty (ii)\\
In the first case, if the tableau in question is not a bad one, then the output of expand is a list containing a single tableau, which is obtained by expanding every node on the leaf level by one step.\\
In the second case, so if the tableau has at least one bad node $n$, the expand function returns two tableaux, each of them differing from the original by an application of the step rule on $n$ according to the nondeterministic behaviour of step on bad nodes.\

One then needs the additional helper function \\

\begin{code}
pairify :: [Tableau] -> [(Tableau, Tableau)]                        
pairify = map \x-> (filter (not . expanded) x , filter expanded x)
\end{code}

which takes a list of tableaux and splits every tableau contained in it into its expanded and nonexpanded parts, yielding a list of pairs of tableaux. Note that, in accordance to the behaviour of our step function, expanded nodes are only stored if they correspond to open branches, therefore, as soon as a tableau has an expanded node, one can be certain that it will not develop into a closed tableau.\

The two functions above are then incorporated in the recursive behaviour of solve, which is given by \\

\begin{code}
solve :: [(Tableau, Tableau)] -> Bool                               
solve []        = False                                             
solve (p:pairs) | null (snd p) && not (null (fst p)) = solve (pairify (expand(fst p))++ pairs)
                | null (snd p) && null (fst p) = True
                | otherwise = solve pairs || False
\end{code}

The idea behind it is the following: given a formula $\varphi$ one starts with a list containing just the pair (T, [ ]) where T corresponds to the initial tableau associated to $\varphi$ (which is different depending on whether one wants to check intuitionistic or classical validity of $\varphi$, and is given by functions which are present in the code) and applies the recursion in solve.\\
The first calculation step will look like
\[\text{solve[(T, [ ])]} \implies \text{solve (pairify (expand(T))}\]
now, if expand(T) has expanded nodes (i.e. fully expanded open branches), then solve will go into its third case and output solve [ ] || False, which yields False. Otherwise, it will continue to operate recursively, generating potentially more than one tableau. The reason why solve takes a list of pairs of tableaux as opposed to a list of tableaux is that one wants to check whether a tableau has fully expanded open branches at each step of the recursion, so that the procedure of expanding a tableau can short-circuit in case it is certain that the tableau will never close. Since the step rule is designed so that a branch is cancelled as soon as it closes, a closing tableau is one that eventually becomes the empty list, therefore our solve function yields True only when given a pair of empty tableaux.\

Note that, given the way the solve function is written, it will work \say{depth-first} in the following sense : if, during the \say{solving}, a list of pairs of tableaux has been generated, the solve function will work by expanding the tableau corresponding to the first pair as much as possible until it either yields a closing tableau (in which case the entire function stops and yields True) or it yields a non-closing tableau, in which case the solve function will turn to expanding the other tableaux in the list.

Lastly we need these for quick usability:\\

\begin{code}
initintuitTab :: Frm -> Tableau                                     
initintuitTab  f = [Nd [] [] [] [] [S (F, f)] [] []]                

intuitthm :: Frm -> Bool                                            
intuitthm f = solve [(initintuitTab f, [])]

intuitsat :: Frm -> Bool                                            
intuitsat f = not ( intuitthm (N f))

initclassTab:: Frm -> Tableau                                       
initclassTab  f = [Nd [] [] [] [] [S (Fc, f)] [] []]              

classthm :: Frm -> Bool                                            
classthm f = solve [(initclassTab f, [])]

classsat :: Frm -> Bool                                            
classsat f = not (classthm (N f))

\end{code}





