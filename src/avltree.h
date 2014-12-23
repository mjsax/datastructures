/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */
#ifndef _AVLTREE_H_
#define _AVLTREE_H_

#include <stddef.h>
#include <limits.h>
#include <exception>
#include <iterator>
#include <cassert>

namespace datastructures {
	namespace avltree {
		class AvltreeException : public std::exception {
			public:
				virtual ~AvltreeException() throw() { /* empty */};
				virtual const char * what() const throw() { return "Value not found."; };
		};

		/*
		 * The node within the AVL-tree. Contains a value and has a pointer to its left and right child as well as to its parent.
		 * The balance factor indicates if left or right sub-tree is deeper.
		 */
		template<class T>
		struct _avlnode {
			const T value;
			_avlnode<T> * child[2]; // index 0 is left child; index 1 is right child
			_avlnode<T> * parent;
			char balanceFactor; // valid values are:
								//	-> -1, if left subtree is deeper then right subtree
								//	-> 0, if both subtrees are equally deep
								//	-> 1, if right subtree is deeper than left subtree

			_avlnode(const T v) throw() : value(v), parent(NULL), balanceFactor(0) {
				child[0] = NULL;
				child[1] = NULL;
			}
			_avlnode(const T v, _avlnode<T> * p) throw() : value(v), parent(p), balanceFactor(0) {
				child[0] = NULL;
				child[1] = NULL;
			}
			~_avlnode() throw() {
				if(child[0] != NULL) {
					delete child[0];
					child[0] = NULL;
				}
				if(child[1] != NULL) {
					delete child[1];
					child[1] = NULL;
				}
			}
		};

		/*
		 * Computes the child index of node with regard to its parent. Return 0 if node is left child of its parent and 1 if
		 * node is right child of its parent (or parent is root). Assumes node is not NULL.
		 *
		 * Complexity: O(1)
		 */
		template<class T>
		inline int _getIndex(const _avlnode<T> * const node) throw() {
			assert(node != NULL);
			const _avlnode<T> * const parent = node->parent;
			// -> parent might be root: in this case, index has no useful value because there is not parent
			//		(left hand side of || for computing index; ensures that right hand side is not evaluated if parent==NULL
			//		 to avoid null pointer access; returned index=1)
			// -> otherwise:
			// 		parent->left == node -> index = 0
			// 		parent->right == node -> index = 1
			//		(right hand side of || for computing index:
			//		 -> parent->child[1] == node evaluates to true => index=1
			//		 -> parent->child[1] == node evaluates to false => index=0)
			return parent == NULL || parent->child[1] == node;
		}


		/*
		 * TODO
		 */
		template<class T>
		class avltree_const_iterator : public std::iterator<std::bidirectional_iterator_tag, T> {
			private:
				typedef _avlnode<T>				avlnode;

				const avlnode * node;
				const avlnode * lastVisited;
			public:

				typedef std::bidirectional_iterator_tag		iterator_category;

				/*
				 * TODO
				 */
				avltree_const_iterator() : node(NULL), lastVisited(NULL) { /* empty */ };
				/*
				 * TODO
				 */
				avltree_const_iterator(const avlnode * n, const avlnode * l) : node(n), lastVisited(l) { /* empty */ };
				/*
				 * TODO
				 */
				avltree_const_iterator(const avltree_const_iterator & it) : node(it.node), lastVisited(it.lastVisited) { /* empty */ };





				/*
				 * TODO
				 */
				const T & operator*() const {
					return node->value;
				}

				/*
				 * TODO
				 */
				const T * operator->() const {
					return &node->value;
				}

				/*
				 * TODO
				 *
				 * Complexity: log(n)
				 */
				avltree_const_iterator<T> & operator++() {
					while(true) {
						// if coming from top, step down to the very left, to get smallest value from subtree
						if(lastVisited == node->parent && node->child[0] != NULL) {
							lastVisited = node;
							node = node->child[0];
							if(node->child[0] == NULL) { // smallest ancestor found, stop iterating
								break;
							}
						} else { // no left child after going down or currently moving up
							// step down to root right subtree, if not coming from it
							if(node->child[1] != NULL && lastVisited != node->child[1]) {
								lastVisited = node;
								node = node->child[1];
								if(node ->child[0] == NULL) {
									// if there is no left subtree, current node is next
									// otherwise, next node is smallest from subtree with current node as subtree root
									break;
								}
							} else { // all children visited; step up
								lastVisited = node;
								if(_getIndex(node) == 0) {
									// if stepping up from left child, current node is next, stop iterating
									node = node->parent;
									break;
								} else {
									node = node->parent;
								}
							}
						}
					}

					return *this;
				}

				/*
				 * TODO
				 *
				 * Complexity: log(n)
				 */
				avltree_const_iterator<T> operator++(int) {
					avltree_const_iterator it(*this);
					++(*this);
					return it;
				}

				/*
				 * TODO
				 *
				 * Complexity: log(n)
				 */
				avltree_const_iterator<T> & operator--() {
					assert(false);

					return *this;
				}

				/*
				 * TODO
				 *
				 * Complexity: log(n)
				 */
				avltree_const_iterator<T> operator--(int) {
					avltree_const_iterator it(*this);
					--(*this);
					return it;
				}

				/*
				 * TODO
				 */
				bool operator==(const avltree_const_iterator<T> & it) const {
					return node == it.node;
				}

				/*
				 * TODO
				 */
				bool operator!=(const avltree_const_iterator<T> & it) const {
					return node != it.node;
				}
		};


		/*
		 * AVL tree container. An AVL tree (named after its inventors, Georgy Adelson-Velsky and Landis') is a sorted, balanced, binary tree.
		 *
		 * avltree requires a total order on the value's type T (specified by "<") and cannot store duplicates. By default, std::less<T> is used
		 * to insert values at the correct position in the tree. If T is a user-defined type/class, it must provide an implementation of
		 * less-than operator: bool operator<(const T &) const
		 *
		 * If pointer types are used, a user-defined comparator C should be provided. Otherwise, values are ordered by their memory addresses.
		 * Furthermore, inserted values must not be modified after inserting. Otherwise, internal tree structure might get invalid. Thus, no
		 * guarantees about tree behavior can be given if values inserted by pointer or reference are modified after insertion.
		 *
		 * A user-defined comparator must provide an implementation of the function call operator that returns true if first parameter is less
		 * than second parameter and false otherwise: bool operator()(const T, const T) const
		 *
		 * Additionally, a key type K can be provided (that is equal to value type by default) that enables key-based find and remove operation.
		 * If a key type is used, a user-defined comparator must be specified that provides three function call operators:
		 *   (1) bool operator()(const T, const T) const;
		 *   (2) bool operator()(const K, const T) const;
		 *   (3) bool operator()(const T, const K) const;
		 * The user-defined comparator must ensure, that all three function call operators return true if the first parameter is less than the
		 * second parameter. Additionally, it must be ensured that for any two used value/key pairs V1/K1 and V2/K2 it must hold that
		 * V1 < V2 <=> K1 < V2 <=> V1 < K2.
		 */

		// TODO: make STL container conform... see http://www.cplusplus.com/reference/stl/
		// TODO: make C++ 11 or C++14 compatible

		template<class T, class C = std::less<T>, class K = T>
		class avltree {
			public:
				typedef avltree_const_iterator<T>				const_iterator;
				typedef std::reverse_iterator<const_iterator>	const_reverse_iterator;


			private:
				typedef _avlnode<T>				avlnode;

				avlnode * root;
				size_t currentSize;
				C less_than;

				template<class T1, class T2>
				inline bool equals(const T1 v1, const T2 v2) const {
					return !(less_than(v1, v2)
							|| less_than(v2, v1));
				}

				/*
				 * Searches for a given value starting at the root. Assumes root is not NULL. Returns founded node or last
				 * visited(!) leaf. Hence, returned node can or cannot contain value---depending if value is stored in tree
				 * or not.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				template<class KT>
				avlnode * findNode(const KT key) const {
					assert(root != NULL);

					const avlnode * node = root;

					while(true) {
						if(equals(key, node->value)) {
							break;
						}

						if(less_than(key, node->value)) {
							if(node->child[0] == NULL) {
								break;
							} else {
								node = node->child[0];
								continue;
							}
						}

						assert(less_than(node->value, key));
						if(node->child[1] == NULL) {
							break;
						} else {
							node = node->child[1];
							continue;
						}
					}

					return const_cast<avlnode *>(node);
				}

				/*
				 * Template function to cover search by value and search by key. Searches for a given value starting at the root.
				 * Returns value if present. Otherwise, an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				template<class KT>
				inline T findInternal(const KT key) const throw(AvltreeException) {
					if(root != NULL) {
						const avlnode * const node = findNode(key);
						assert(node != NULL);

						if(equals(key, node->value)) {
							return node->value;
						}
					}

					throw AvltreeException();
				}

				/*
				 * Replaces a child of given parent node by an arbitrary sub-tree. Index indicates if left (index==0) or right (index==1)
				 * child should be replaced. Child is removed from tree (ie, its parent, but keeps all other links). Parent becomes
				 * subtree's parent (if subtree is present).
				 *
				 * Complexity: O(1)
				 */
				inline void replaceChildBySubtree(avlnode * const parent, const int index, avlnode * const subtree) throw() {
					assert(index == 0 || index == 1);

					if(parent != NULL) { // node is NOT root
						parent->child[index] = subtree;
					} else { // node is root
						root = subtree;
					}

					// fix parent pointer
					if(subtree != NULL) {
						subtree->parent = parent;
					}
				}

				/*
				 * Moves given node one level upwards the tree. Parent is move one level downwards. Index indicates if shifting has to be
				 * done from left to right (index==0) or from right to left (index==1). Potential left or right sub-tree of node becomes
				 * right or left sub-tree of parent. Assumes that node is not NULL and that node has a parent.
				 *
				 * Complexity: O(1)
				 */
				inline void rotateSimple(avlnode * const node, const int index) throw() {
					assert(node != NULL);
					assert(node->parent != NULL);
					assert(index == 0 || index == 1);

					// sanity check: it not true, rotating does not make sense
					assert(node->child[index] != NULL);

					avlnode * const parent = node->parent;

					// sanity check for input balance factors: computation of new balance factors is based on this assumptions
					assert(node->balanceFactor != 0 || (index==0 && parent->balanceFactor==-1) || (index==1 && parent->balanceFactor==1));



					// rotate node up (ie, replace parent by node)
					replaceChildBySubtree(parent->parent, _getIndex(parent), node);

					// move sub-tree of node to be parent's sub-tree
					// -> index==0 => node->right becomes parent->left
					// -> index==1 => node->left becomes parent->right
					replaceChildBySubtree(parent, index, node->child[1-index]);

					// rotate parent down (below node)
					// -> index==0 => rotate from left to right => parent becomes right child of node
					// -> index==1 => rotate from right to left => parent becomes left child of node
					replaceChildBySubtree(node, 1-index, parent);



					// correct balance factors

					// there are 6 different cases: [(1) summarizes 4 cases]
					//   1) node->balanceFactor != 0
					//		in this cases, we have a left-left or right-right situation
					//		(possible after insert in left/right side of node or remove in right/left side of parent)
					//      -> after rotating, node and parent are in balance (nbf = pbf = 0)
					//
					//   2) node->balanceFactor == 0 && index == 0
					//      in this cases, we have a remove situation on the right hand side of parent
					//      -> after rotating, parent keeps it balance factor but node's right hand side increases by one (nbf = 1)
					//
					//   3) node->balanceFactor == 0 && index == 1
					//      symmetric to case (2)
					//      -> balance factor but node's right hand side decreases by one (nbf = -1)
					//
					// we unify all cases as follows:
					//   because case (2) and (3) are remove cases, it holds that:
					//     index==0 => parent->balanceFactor==-1
					//     index==1 => parent->balanceFactor==1
					//   hence, the new balance factor of node is "parent->balanceFactor * -1"
					//
					// in case (1) "(1 - nbf*nbf)==0"; thus, both balance factors are set to zero
					// in case (2) and (3) "(1 - nbf*nbf)==1"; thus, parent->balance factor is not altered and node->balanceFactor is inverted

					const int nbf = node->balanceFactor;
					const int pbf_new = (1 - nbf*nbf) * parent->balanceFactor;

					// note that after rotation, node is on top of parent
					node->balanceFactor = -pbf_new;
					parent->balanceFactor = pbf_new;
				}

				/*
				 * Moves child of given node two level upward (above node), and moves node's parent one level down (become child of
				 * node's child that was moved up). Index indicates if shifting of child hat to be done left-right (index==0) or
				 * right-left (index==1). Potential sub-trees of child become sub-trees of node and parent. Assume node is not NULL,
				 * node has a parent, and left or right child (index==1 or index==0, respectively) of node is present.
				 *
				 * Complexity: O(1)
				 */
				inline void rotateDouble(avlnode * const node, const int index) throw() {
					assert(node != NULL);
					assert(node->parent != NULL);
					assert(node->child[1-index] != NULL);
					assert(index == 0 || index == 1);

					avlnode * const parent = node->parent;
					avlnode * const child = node->child[1-index];

					// double-rotate child up (ie, replace parent by child)
					replaceChildBySubtree(parent->parent, _getIndex(parent), child);

					// first sub-tree of child is moved below node
					// -> index==0 => left sub-tree of child becomes right sub-tree of node
					// -> index==1 => right sub-tree of child becomes left sub-tree of node
					replaceChildBySubtree(node, 1-index, child->child[index]);

					// move node below child
					// -> index==0 => node becomes left child of child
					// -> index==1 => node becomes right child of child
					replaceChildBySubtree(child, index, node);

					// second sub-tree of child is moved below parent
					// -> index==0 => right sub-tree of child becomes left sub-tree of parent
					// -> index==1 => left sub-tree of child becomes right sub-tree of parent
					replaceChildBySubtree(parent, index, child->child[1-index]);

					// move parent below child
					// -> index==0 => parent becomes right child of child
					// -> index==1 => parent becomes left child of child
					replaceChildBySubtree(child, 1-index, parent);



					// correct balance factors

					// there are three cases:
					//   1) child->balanceFactor == 0
					//      in this case, both subtrees of child and the outer subtrees of node and parent are equally deep
					//      -> after rotation, all balance factors are zero
					//   2) child->balanceFactor == 1
					//      in this case, the left subtree of child is less deep (by one) as the right subtree (which is equally deep as the outer subtrees of node and parent)
					//      -> after rotation, the short left subtree is below (right side) of the left child of the new top node
					//      -> balance factor of left child of the new top node is 1
					//   3) child->balanceFactor == -1
					//		symmetric to case (2)
					//      -> balance factor of right child of the new top node is -1
					//
					// we unify all cases as follows:
					//   child->balanceFactor==1 OR child->balanceFactor==-1
					//      => childSqaure==1 (does not alter right factor)
					//   child->balanceFactor==1
					//		=> newLeft = "(child->balanceFactor + 1) / -2 == -1
					//      => newRight = newLeft + 1 = 0
					//   child->balanceFactor==-1
					//      => "(child->balanceFactor + 1) / -2 == 0
					//      => newRight = newLeft + 1 = 1
					//   child->balanceFactor==0
					//     => childSqaure==0 (ensures the right hand side is invalidated)
					//     => instead of adding 1, 0 is added to compute new right hand side balance factor

					const int cbf = child->balanceFactor;
					const int childSqaure = cbf * cbf;
					const int balanceLeftChild = childSqaure * ((cbf+1)/-2);

					// note that after rotation, child is on top of node and parent
					child->child[0]->balanceFactor = balanceLeftChild;
					child->child[1]->balanceFactor = balanceLeftChild + childSqaure;
					child->balanceFactor = 0; // child is always in balance
				}

				/*
				 * Balances the tree, starting at node (inclusive) up to subtreeRoot (exclusive). Hence, balancing the complete
				 * tree requires subtreeRoot to be NULL. Node must be below subtreeRoot within tree. Index indicates if node's
				 * left (index==0) or node's right (index==1) child's height changed (that triggered re-balancing node).
				 * InsertRemove indicate if the change in node's child was an insert operation (insertRemove==0) or a remove
				 * operation (insertRemove==1).
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				int balanceSubtree(const avlnode * const subtreeRoot, avlnode * node, int index, const int insertRemove) throw() {
					assert(index == 0 || index == 1);
					assert(insertRemove == 0 || insertRemove == 1);

					while(node != subtreeRoot) {  // move up to root...
						assert(node != NULL);

						// if we insert in left child or remove from right child, we need to rotate from left to right (rotate==0)
						// if we insert in right child or remove from left child, we need to rotate from right to left (rotate==1)
						const int rotate = 1 - (index == insertRemove);
						// if we insert in left child or remove from right child, height need to be increase (heightChange==1)
						// if we insert in right child or remove from left child, height need to be decrease (heightChange==-1)
						const int heightChange = -1 + 2*rotate;
						// if we insert, we terminate if node balance factor is 0 (term==0)
						// if we remove from left child, we terminate if node is in acceptable in-balance (term==1)
						// if we remove from right child, we terminate if node is in acceptable in-balance (term==-11)
						// -> depth did not change; hence, there is nothing to propagate upwards
						const int term = -insertRemove + 2*insertRemove*rotate;

						const int bf = node->balanceFactor + heightChange;

						if(bf == term) {
							node->balanceFactor = bf;
							return 0;
						}

						if(bf == 2*heightChange) { // tree is not in balance -> need to rotate
							avlnode * const child = node->child[rotate];
							if(child->balanceFactor == -heightChange) {
								// more difficult case: rotation at two different levels is necessary (including split of child subtree)
								// starting point: [parent is on top]
								//   child <- node <- parent (left-right in-balance)
								// or
								//   parent -> node -> child (right-left in-balance)
								// is rotated to: node <- child -> parent [child is on top]
								rotateDouble(child, rotate);
							} else {
								// simple case: single right rotation is sufficient
								// starting point: [parent is on top]
								//   child <- node <- parent (left-left in-balance)
								// or
								//   parent -> node -> child (right-right in-balance)
								// is rotated to: [node is on top]
								//   child <- node -> parent
								//   (right sub-tree of node becomes left sub-tree of parent)
								// or
								//   parent <- node -> child
								//   (left sub-tree of node becomes right sub-tree of parent)
								assert(child->balanceFactor == 0 || child->balanceFactor == heightChange);
								rotateSimple(child, rotate);
							}
							node = node->parent;

							if(node->balanceFactor == -term) {
								return 0;
							}
						} else {
							// tree height changed by one
							// -> no in-balance, no rotation
							// need to propagate change upwards
							node->balanceFactor = bf;
						}

						// step to parent
						index = _getIndex(node);
						node = node->parent;
					}

					// we reached the root of subtree; hence, our height changed by one
					return 1;
				}

				/*
				 * Return the ancestor of a node with the smallest or largest value. If index==0, the smallest ancestor is returned.
				 * If index==1, the largest ancestor is returned. If node is NULL, NULL is returned. If node has no children, node
				 * is returned.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				inline avlnode * findLimitAncestor(const avlnode * node, const int index) const throw() {
					assert(index == 0 || index == 1);

					if(node == NULL)
						return NULL;

					while(node->child[index] != NULL) {
						node = node->child[index];
					}

					return const_cast<avlnode*>(node);
				}

				/*
				 * Removes a given node from the tree. If left subtree is present, node is replaced by largest ancestor of it
				 * to maintain tree order. Otherwise, node is simply removed. Tree re-balancing might occur.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				void removeNode(const avlnode * const node) throw() {
					assert(node != NULL);

					int index = _getIndex(node);
					avlnode * largestAncestor = findLimitAncestor(node->child[0], 1);

					if(largestAncestor != NULL) {
						avlnode * const p_ancestor = largestAncestor->parent;

						// remove largest child from subtree
						int heightDifferenz = 0;
						if(p_ancestor != node) { // regular case
							// replace ancestor by its left sub-tree (in order to remove ancestor from tree)
							replaceChildBySubtree(p_ancestor, 1, largestAncestor->child[0]);

							// check for special case, in which left hand child (of node that is remove) has a single right leaf-child
							// in this case, replaceChildBySubtree(...), decreased subtree height by one
							heightDifferenz = p_ancestor == node->child[0] && p_ancestor->child[0] == NULL;

							// balance subtree upward to the node that is removed
							heightDifferenz += balanceSubtree(node, p_ancestor, 1, 1);
						} else { // ancestor is direct child of node
							// replace ancestor by its left sub-tree
							replaceChildBySubtree(p_ancestor, 0, largestAncestor->child[0]);
							heightDifferenz = 1;
						}

						// use largest ancestor to replace node to be removed
						replaceChildBySubtree(largestAncestor, 0, node->child[0]);
						replaceChildBySubtree(largestAncestor, 1, node->child[1]);
						replaceChildBySubtree(node->parent, index, largestAncestor);
						largestAncestor->balanceFactor = node->balanceFactor;

						if(heightDifferenz == 0)
							return;

						index = 0; // lower tree is left child (prepare for balanceSubtree(...))
					} else { // node has no left subtree or left subtree is exactly one node
						// replace node by subtree
						replaceChildBySubtree(node->parent, index, node->child[1]);

						// start re-balancing upper tree above node, because node is not present any longer
						largestAncestor = node->parent;
					}

					// balance tree upward to root starting at removed node (ie, its replacement or its parent)
					balanceSubtree(NULL, largestAncestor, index, 1);
				}

				/*
				 * Removes a given node from the tree, deletes the allocated node memory, and returns the value contained in the node.
				 */
				T removeNodeInternal(avlnode * const node) throw() {
					removeNode(node);

					const T value = node->value;
					// set children to NULL -> otherwise, "delete node" recursively deletes children nodes
					node->child[0] = NULL;
					node->child[1] = NULL;
					delete node;

					if(currentSize < UINT_MAX) {
						assert(currentSize > 0);
						--currentSize;
					} else if(root == NULL) {
						assert(currentSize == UINT_MAX);
						currentSize = 0;
					}

					return value;
				}

				/*
				 * Template function to cover remove by value and remove by key. Removes a value from a tree by given key or value. Searches for the
				 * value to be removed starting at the root. Returns removed value if present. Otherwise, an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				template<class KT>
				T removeInternal(const KT value) throw(AvltreeException) {
					if(root != NULL) {
						avlnode * const node = findNode(value);
						assert(node != NULL);

						if(equals(value, node->value)) {
							return removeNodeInternal(node);
						}
					}

					throw AvltreeException();
				}

			public:
				avltree() : root(NULL), currentSize(0) { /* empty */ }
				~avltree() {
					if(root != NULL)
						delete root;
				}

				// TODO: remove (only for debugging)
				const avlnode * const getRoot() const throw() {
					return root;
				}

				/*
				 * Inserts a new value into the tree. If value is already present, tree is not altered and false is returned.
				 * If value is not present, it is inserted (including possible re-balancing of the tree) and true is returned.
				 *
				 * In case of memory allocation error, tree is not altered and and bad_alloc exception is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				bool insert(const T value) throw(std::bad_alloc) {
					if(root != NULL) {
						avlnode * const node = findNode(value);
						assert(node != NULL);

						if(equals(value, node->value)) { // duplicate found; returned leaf contains value
							return false;
						}

						// we insert below returned leaf
						const int index = !less_than(value, node->value); // value < node->value => index = 0; index = 1, otherwise
						assert(node->child[index] == NULL);

						node->child[index] = new avlnode(value, node);
						if(node->child[index] == NULL) {
							throw std::bad_alloc();
						}

						balanceSubtree(NULL, node, index, 0);
					} else {
						assert(currentSize == 0);

						// else: empty tree; create new root
						root = new avlnode(value);
						if(root == NULL) {
							throw std::bad_alloc();
						}
					}

					if(currentSize < UINT_MAX) {
						++currentSize;
					}

					return true;
				}

				/*
				 * Searches for a value in the tree by value. Returns a copy of the value if present; otherwise an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				T find(const T value) const throw(AvltreeException) {
					return findInternal(value);
				}

				/*
				 * Searches for a value in the tree by key. Returns a copy of the value if present; otherwise an AvltreeException is thrown.
				 * By default (ie, if no key type template parameter is specified), findByKey() is the same as find().
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				T findByKey(const K key) const throw(AvltreeException) {
					return findInternal(key);
				}

				/*
				 * Removes a value from the tree. Returns a copy of the removed value if present; otherwise an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				T remove(const T value) throw(AvltreeException) {
					return removeInternal(value);
				}

				/*
				 * Removes a value from the tree by given key. Returns a copy of the removed value if present; otherwise an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				T removeByKey(const K key) throw(AvltreeException) {
					return removeInternal(key);
				}

				/*
				 * Removes all values from the tree.
				 */
				void clear() throw() {
					if(root != NULL) {
						delete root;
						root = NULL;
						currentSize = 0;
					}
				}

				bool empty() const throw() {
					return root == NULL;
				}

				/*
				 * Returns the current number of values contained in the tree. The count is only correct, if the tree always contained less than UINT_MAX values.
				 * If UINT_MAX or more values have been contained in the tree, size() returns UINT_MAX (even if the current number of values is less than UINT_MAX).
				 * The count is automatically corrected, if the tree gets empty. If this case, the count is set to zero. The count can be recomputed using
				 * recomputeSize().
				 *
				 * Complexity: O(1)
				 */
				size_t size() const throw() {
					return currentSize;
				}

				/*
				 * Recomputes the number of values contained in the tree and return the count. If more than UINT_MAX values are contained, UINT_MAX in returned.
				 *
				 * Complexity: O(n) with n being the current number of values contained in the tree.
				 */
				// TODO: introduce treeDepth -> use to chance recomputing if depth is too large, s.th. size must be smaller than UINT_MAX
				// TODO: introduce count for each node that contains #elements for the subtree
				size_t recomputeSize() throw() {
					size_t newSize = 0;

					if(root != NULL) {
						const avlnode * node = root;
						const avlnode * lastVisited = NULL;
						++newSize;

						while(node != NULL) {
							if(lastVisited == node->parent) {
								lastVisited = node;
								if(node->child[0] != NULL) {
									node = node->child[0];
									++newSize;
								} else if(node->child[1] != NULL) {
									node = node->child[1];
									++newSize;
								} else {
									node = node->parent;
								}
							} else if(lastVisited == node->child[0]) {
								lastVisited = node;
								if(node->child[1] != NULL) {
									node = node->child[1];
									++newSize;
								} else {
									node = node->parent;
								}
							} else {
								assert(lastVisited == node->child[1]);
								lastVisited = node;
								node = node->parent;
							}
						}
					}

					currentSize = newSize;
					return currentSize;
				}

				/*
				 * Returns the smallest values stored in the tree. If tree in empty, an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				const T & front() const throw(AvltreeException) {
					const avlnode * const min = findLimitAncestor(root, 0);

					if(min != NULL) {
						return min->value;
					}

					throw AvltreeException();
				}

				/*
				 * Removes the smallest values stored in the tree and returns it. If tree in empty, an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				T pop() throw(AvltreeException) {
					avlnode * const min = findLimitAncestor(root, 0);

					if(min != NULL) {
						return removeNodeInternal(min);
					}

					throw AvltreeException();
				}

				/*
				 * Returns the largest values stored in the tree. If tree in empty, an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				T back() const throw(AvltreeException) {
					const avlnode * const max = findLimitAncestor(root, 1);

					if(max != NULL) {
						return max->value;
					}

					throw AvltreeException();
				}

				/*
				 * TODO
				 */
				const_iterator cbegin() const throw() {
					const avlnode * min = findLimitAncestor(root, 0);

					return min != NULL ? const_iterator(min, min->parent) : const_iterator();
				}

				/*
				 * TODO
				 */
				const_iterator cend() const throw() {
					const avlnode * max = findLimitAncestor(root, 1);
					if(max != NULL) {
						if(max->child[1] != NULL) {
							return const_iterator(max, max->child[1]);
						}
						if(max->child[0] != NULL) {
							return const_iterator(max, max->child[0]);
						}
						return const_iterator(max, max->parent);
					}
					return const_iterator();
				}

				/*
				 * TODO
				 */
				const_iterator crbegin() const throw() {
					const avlnode * max = findLimitAncestor(root, 1);
					return max != NULL ? const_iterator(max, NULL) : const_iterator();
				}

				/*
				 * TODO
				 */
				const_iterator crend() const throw() {
					return cbegin();
				}

		};

		/*
		 * TODO
		 */
		template<typename T>
		inline bool operator==(const avltree_const_iterator<T> & it1, const avltree_const_iterator<T> & it2) {
			return it1.node == it2.node;
		}

		/*
		 * TODO
		 */
		template<typename T>
		inline bool operator!=(const avltree_const_iterator<T> & it1, const avltree_const_iterator<T> & it2) {
			return it1.node != it2.node;
		}

	}
}

#endif
