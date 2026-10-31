<!-- SPDX-License-Identifier: GPL-3.0-only
Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. -->
Modify the current ASM implementation Rocq-copy/LPL/ASM/. 

Alter the structure of ASM: 
- Simply the state of ASM: A state does not contain any variable-value pairs. It only contains a set of propositions (as the old one). 
- Remove the function for entirely encoding an ASM into a regular program. We do not need it for deductions. We only need unfold_at. Remove the old benchmarks that rely on this function. 
- Adapt all the files in ASM to these changes: remove any redundant parts; revise the places that need to be updated accordingly.  


- If cannot remove any files, write the cmd needed for the user to execute to remove the files in a .txt file so that the user can execute it manually. Also tell the user how to use the cmd in this file. 
- If having any problems, stop and interact with the user before proceeding. 