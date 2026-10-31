<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
Revise the current LPL theory in Rocq-copy/LPL. 

## Requirements

Read the sub-folder `key`, understand how the KeY tool allows DIY structures in its dynamic logic theory. 
Then figure out how can we support DIY structures in the current LPL theory. 
We need:
- extends the current LPL theory to support DIY structures. Figure out how can we allow extra user-defined structures, such as sorts, predicates, functions, etc., and also `updates` in LPL that relates to the labels, just as in KeY. (Note that you need to think about whether this is feasible within the existing framework) 
- If not possible, explain to me the reasons; If possible, show me the plan how to do it. If not clear, interact with the user. 
- After having an idea how to do it, adjust the rest of the current LPL theory to make everything right. 

## Other Requirements

- Check integrity, remove redundant parts after the revision. 
- Add into the plan that put the content of this plan into a .md file before implementing it. 