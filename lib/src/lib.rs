//======---------------------------------------------------------------======//
// Copyright (c) 2022 Evan Cox <evanacox00@gmail.com>.                       //
//                                                                           //
// Licensed under the Apache License, Version 2.0 (the "License");           //
// you may not use this file except in compliance with the License.          //
// You may obtain a copy of the License at                                   //
//                                                                           //
//     http://www.apache.org/licenses/LICENSE-2.0                            //
//                                                                           //
// Unless required by applicable law or agreed to in writing, software       //
// distributed under the License is distributed on an "AS IS" BASIS,         //
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  //
// See the License for the specific language governing permissions and       //
// limitations under the License.                                            //
//======---------------------------------------------------------------======//

#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(rustdoc::private_intra_doc_links)]

//! # Quartz
//!
//! Quartz is a compiler middle- and back-end library in the same vein as LLVM or Cranelift.
//!
//! This crate contains the APIs necessary to create, manipulate, and compile Quartz IR (QIR),
//! the IR format used throughout the project.

pub mod ir;
pub mod prelude;

/// Adds two numbers together.
///
/// ## Example
/// ```
/// use quartz::add_two;
///
/// let result = add_two(2, 2);
/// assert_eq!(result, 4);
/// ```
pub fn add_two(x: i32, y: i32) -> i32 {
    x + y
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add_two(2, 2);

        assert_eq!(result, 4);
    }
}
