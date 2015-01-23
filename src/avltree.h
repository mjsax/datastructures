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
#include <cassert>

/**
 * \brief The top-level namespace of the whole project
 */
namespace datastructures {
	/**
	 * \brief The namespace of the AVL-Tree.
	 */
	namespace avltree {
		/**
		 * \brief This exception is thrown if a requested element cannot be found in the tree.
		 */
		class AvltreeException : public std::exception {
			public:
				virtual ~AvltreeException() throw() { /* empty */};
				virtual const char* what() const throw() { return "Value not found."; };
		};

		///
		/// \cond
		///
		/*
		 * The base node within the AVL-tree. Contains a pointer to its parent, left and right child, as well as left and right sibling.
		 * The balance factor indicates if left or right sub-tree is deeper.
		 */
		struct _avlbasenode {
			_avlbasenode* parent;
			_avlbasenode* child[2]; // index 0 is left child; index 1 is right child

			_avlbasenode* prev;
			_avlbasenode* next;

			char balanceFactor; // valid values are:
								//	-> -1, if left subtree is deeper then right subtree
								//	-> 0, if both subtrees are equally deep
								//	-> 1, if right subtree is deeper than left subtree

			/*
			 * Creates a dummy base node. Used as before-first, after-last, and as empty node in iterators in case of empty tree.
			 */
			_avlbasenode() : parent(NULL), prev(this), next(this), balanceFactor(0) {
				child[0] = NULL;
				child[1] = NULL;
			}
			/*
			 * Creates a new node given its parent in the tree and links the new node in between two other nodes. Nodes are always created as leafs,
			 * thus, children are always NULL.
			 */
			_avlbasenode(_avlbasenode* p, _avlbasenode& before, _avlbasenode& after) : parent(p), prev(&before), next(&after), balanceFactor(0) {
				child[0] = NULL;
				child[1] = NULL;
				before.next = this;
				after.prev = this;
			}
			/*
			 * Frees memory of child nodes if present. Thus, all nodes of the complete subtree will automatically be freed by recursive destructor calls.
			 */
			virtual ~_avlbasenode() throw() {
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
		 * The node within the AVL-tree. Contains a value and inherits all tree-structure pointers from base node.
		 */
		template<class T>
		struct _avlnode : _avlbasenode {
			const T value;

			/*
			 * Creates a new node for value v, given its parent in the tree and links the new node in between two other nodes.
			 * Nodes are always created as leafs, thus, children are always NULL.
			 */
			_avlnode(const T& v, _avlbasenode& before, _avlbasenode& after, _avlbasenode* p) throw() : _avlbasenode(p, before, after), value(v) { /* empty */}
		};
		///
		/// \endcond
		///



		template<class T, class C = std::less<T>, class K = T> class avltree;

		/**
		 * \brief Iterator for @ref avltree.
		 *
		 * Read-only iterator that can move forward and backward. De-referencing an iterator might result in _undefined behavior_
		 * if iterator was retrieved from an empty tree, or is at position _before-the-first-element_ or _after-the-last-element_.
		 * Because the internal tree structure ensures an ordered insert and retrieval, only read-only (const) iterator is supported.
		 */
		template<class T, class C = std::less<T>, class K = T>
		class _avltree_const_iterator {
			friend class avltree<T,C,K>;
			public:
				typedef int									difference_type; // TODO: check standard

			private:
				typedef _avltree_const_iterator				self;
				typedef const _avltree_const_iterator		cself;
				typedef _avltree_const_iterator&			selfref;
				typedef const _avltree_const_iterator&		cselfref;

				typedef _avlnode<T>							avlnode;

				_avlbasenode empty; // dummy node that is used for iterator on empty tree
				const _avlbasenode* node; // the current element the iterator is pointing to

			public:
				typedef std::bidirectional_iterator_tag		iterator_category;
				typedef T									value_type;
				typedef const T*							pointer;
				typedef const T&							reference;

				/**
				 * \brief Constructs an empty iterator no associated with any @ref avltree.
				 *
				 * An empty iterator is non-movable and non-readable.
				 */
				_avltree_const_iterator() : node(&empty) {  }
			private:
				/**
				 * \brief Constructs an iterator that points to node n.
				 */
				_avltree_const_iterator(const _avlbasenode* n) : node(n) { /* empty */ }




			public:
				/**
				 * \brief Returns the value of the element of the current iterator position.
				 *
				 * Must not be called if iterator is at position _before-the-first-element_ or _after-the-last-element_.
				 * Furthermore, it must not be called if the iterator was retrieved from an empty tree.
				 */
				reference operator*() const {
					assert(dynamic_cast<const avlnode* const>(node) != NULL);
					return static_cast<const avlnode* const>(node)->value;
				}

				/**
				 * \brief Returns the value of the element of the current iterator position.
				 *
				 * Must not be called if iterator is at position _before-the-first-element_ or _after-the-last-element_.
				 * Furthermore, it must not be called if the iterator was retrieved from an empty tree.
				 */
				pointer operator->() const {
					assert(dynamic_cast<const avlnode* const>(node) != NULL);
					return &static_cast<const avlnode* const>(node)->value;
				}

				/**
				 * \brief Moves the iterator to the next position in forward direction and returns an iterator
				 * pointing to the new position.
				 *
				 * If iterator is at the position _after-the-last-element_ it remains at this position.
				 *
				 * Complexity: O(1)
				 */
				selfref operator++() {
					node = node->next;
					return *this;
				}

				/**
				 * \brief Moves the iterator to the next position in forward direction and returns an iterator
				 * pointing to the original position.
				 *
				 * If iterator is at the position _after-the-last-element_ it remains at this position.

				 * Complexity: O(1)
				 */
				self operator++(int) {
					_avltree_const_iterator it(*this);
					node = node->next;
					return it;
				}

				/**
				 * \brief Moves the iterator to the next position in backward direction and returns an iterator
				 * pointing to the new position.
				 *
				 * If iterator is at the position _before-the-first-element_ it remains at this position.
				 *
				 * Complexity: O(1)
				 */
				selfref operator--() {
					node = node->prev;
					return *this;
				}

				/**
				 * \brief Moves the iterator to the next position in backward direction and returns an iterator
				 * pointing to the original position.
				 *
				 * If iterator is at the position _before-the-first-element_ it remains at this position.
				 *
				 * Complexity: O(1)
				 */
				self operator--(int) {
					_avltree_const_iterator it(*this);
					node = node->prev;
					return it;
				}

				/**
				 * \brief Equality operator.
				 *
				 * Returns `true` if both iterators operate on the same @ref avltree and point to the same
				 * position. Otherwise, `false` is returned.
				 */
				bool operator==(cselfref it) const {
					return node == it.node;
				}

				/**
				 * \brief Inequality operator.
				 *
				 * Returns `true` if both iterators operate on different @ref avltree or point to different
				 * position within the same @ref avltree. Otherwise, `false` is returned.
				 */
				bool operator!=(cselfref it) const {
					return !operator==(it);
				}
		};

		/**
		 * \brief Base class for @ref avltree.
		 *
		 * Contains all value type parameter independent functions.
		 */
		class avltree_base {
			protected:
				///
				/// \cond
				///
				_avlbasenode* root;
				_avlbasenode beforeFirst;
				_avlbasenode afterLast;
				size_t currentSize;

				//const _avlbasenode emptyTreeNode; // dummy node that is used for iterator on empty tree
				///
				/// \endcond
				///

				/**
				 * \brief Creates an empty tree.
				 */
				avltree_base() : root(NULL), currentSize(0) {
					beforeFirst.next = &afterLast;
					afterLast.prev = &beforeFirst;
				}
				/**
				 * \brief Frees all internal nodes allocated by the tree.
				 */
				virtual ~avltree_base() {
					if(root != NULL)
						delete root;
				}

				///
				/// \cond
				///
				/*
				 * Computes the child index of node with regard to its parent. Return 0 if node is left child of its parent and 1 if
				 * node is right child of its parent (or parent is root).
				 *
				 * Complexity: O(1)
				 */
				inline int _getIndex(const _avlbasenode& node) throw() {
					const _avlbasenode* const parent = node.parent;
					// -> parent might be root: in this case, index has no useful value because there is not parent
					//		(left hand side of || for computing index; ensures that right hand side is not evaluated if parent==NULL
					//		 to avoid null pointer access; returned index=1)
					// -> otherwise:
					// 		parent->left == node -> index = 0
					// 		parent->right == node -> index = 1
					//		(right hand side of || for computing index:
					//		 -> parent->child[1] == node evaluates to true => index=1
					//		 -> parent->child[1] == node evaluates to false => index=0)
					return parent == NULL || parent->child[1] == &node;
				}

				/*
				 * Replaces a child of given parent node by an arbitrary sub-tree. Index indicates if left (index==0) or right (index==1)
				 * child should be replaced. Child is removed from tree (ie, its parent, but keeps all other links). Parent becomes
				 * subtree's parent (if subtree is present).
				 *
				 * Complexity: O(1)
				 */
				inline void replaceChildBySubtree(_avlbasenode* const parent, const int index, _avlbasenode* const subtree) throw() {
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
				 * right or left sub-tree of parent. Assumes that node has a parent.
				 *
				 * Complexity: O(1)
				 */
				inline void rotateSimple(_avlbasenode& node, const int index) throw() {
					// sanity check: if not true, rotating does not make sense
					assert(node.child[index] != NULL);

					assert(index == 0 || index == 1);
					assert(node.parent != NULL);
					_avlbasenode& parent = *node.parent;

					// sanity check for input balance factors: computation of new balance factors is based on this assumptions
					assert(node.balanceFactor != 0 || (index==0 && parent.balanceFactor==-1) || (index==1 && parent.balanceFactor==1));



					// rotate node up (ie, replace parent by node)
					replaceChildBySubtree(parent.parent, _getIndex(parent), &node);

					// move sub-tree of node to be parent's sub-tree
					// -> index==0 => node.right becomes parent.left
					// -> index==1 => node.left becomes parent.right
					replaceChildBySubtree(&parent, index, node.child[1-index]);

					// rotate parent down (below node)
					// -> index==0 => rotate from left to right => parent becomes right child of node
					// -> index==1 => rotate from right to left => parent becomes left child of node
					replaceChildBySubtree(&node, 1-index, &parent);



					// correct balance factors

					// there are 6 different cases: [(1) summarizes 4 cases]
					//   1) node.balanceFactor != 0
					//		in this cases, we have a left-left or right-right situation
					//		(possible after insert in left/right side of node or remove in right/left side of parent)
					//      -> after rotating, node and parent are in balance (nbf = pbf = 0)
					//
					//   2) node.balanceFactor == 0 && index == 0
					//      in this cases, we have a remove situation on the right hand side of parent
					//      -> after rotating, parent keeps it balance factor but node's right hand side increases by one (nbf = 1)
					//
					//   3) node.balanceFactor == 0 && index == 1
					//      symmetric to case (2)
					//      -> balance factor but node's right hand side decreases by one (nbf = -1)
					//
					// we unify all cases as follows:
					//   because case (2) and (3) are remove cases, it holds that:
					//     index==0 => parent.balanceFactor==-1
					//     index==1 => parent.balanceFactor==1
					//   hence, the new balance factor of node is "parent.balanceFactor * -1"
					//
					// in case (1) "(1 - nbf*nbf)==0"; thus, both balance factors are set to zero
					// in case (2) and (3) "(1 - nbf*nbf)==1"; thus, parent.balance factor is not altered and node.balanceFactor is inverted

					const int nbf = node.balanceFactor;
					const int pbf_new = (1 - nbf*nbf) * parent.balanceFactor;

					// note that after rotation, node is on top of parent
					node.balanceFactor = -pbf_new;
					parent.balanceFactor = pbf_new;
				}

				/*
				 * Moves child of given node two level upward (above node), and moves node's parent one level down (become child of
				 * node's child that was moved up). Index indicates if shifting of child hat to be done left-right (index==0) or
				 * right-left (index==1). Potential sub-trees of child become sub-trees of node and parent. Assume that
				 * node has a parent and that either the left or right child (index==1 or index==0, respectively) of node is present.
				 *
				 * Complexity: O(1)
				 */
				inline void rotateDouble(_avlbasenode& node, const int index) throw() {
					assert(index == 0 || index == 1);

					assert(node.parent != NULL);
					_avlbasenode& parent = *node.parent;
					assert(node.child[1-index] != NULL);
					_avlbasenode& child = *node.child[1-index];

					// double-rotate child up (ie, replace parent by child)
					replaceChildBySubtree(parent.parent, _getIndex(parent), &child);

					// first sub-tree of child is moved below node
					// -> index==0 => left sub-tree of child becomes right sub-tree of node
					// -> index==1 => right sub-tree of child becomes left sub-tree of node
					replaceChildBySubtree(&node, 1-index, child.child[index]);

					// move node below child
					// -> index==0 => node becomes left child of child
					// -> index==1 => node becomes right child of child
					replaceChildBySubtree(&child, index, &node);

					// second sub-tree of child is moved below parent
					// -> index==0 => right sub-tree of child becomes left sub-tree of parent
					// -> index==1 => left sub-tree of child becomes right sub-tree of parent
					replaceChildBySubtree(&parent, index, child.child[1-index]);

					// move parent below child
					// -> index==0 => parent becomes right child of child
					// -> index==1 => parent becomes left child of child
					replaceChildBySubtree(&child, 1-index, &parent);



					// correct balance factors

					// there are three cases:
					//   1) child.balanceFactor == 0
					//      in this case, both subtrees of child and the outer subtrees of node and parent are equally deep
					//      -> after rotation, all balance factors are zero
					//   2) child.balanceFactor == 1
					//      in this case, the left subtree of child is less deep (by one) as the right subtree (which is equally deep as the outer subtrees of node and parent)
					//      -> after rotation, the short left subtree is below (right side) of the left child of the new top node
					//      -> balance factor of left child of the new top node is 1
					//   3) child.balanceFactor == -1
					//		symmetric to case (2)
					//      -> balance factor of right child of the new top node is -1
					//
					// we unify all cases as follows:
					//   child.balanceFactor==1 OR child.balanceFactor==-1
					//      => childSqaure==1 (does not alter right factor)
					//   child.balanceFactor==1
					//		=> newLeft = "(child.balanceFactor + 1) / -2 == -1
					//      => newRight = newLeft + 1 = 0
					//   child.balanceFactor==-1
					//      => "(child.balanceFactor + 1) / -2 == 0
					//      => newRight = newLeft + 1 = 1
					//   child.balanceFactor==0
					//     => childSqaure==0 (ensures the right hand side is invalidated)
					//     => instead of adding 1, 0 is added to compute new right hand side balance factor

					const int cbf = child.balanceFactor;
					const int childSqaure = cbf * cbf;
					const int balanceLeftChild = childSqaure * ((cbf+1)/-2);

					// note that after rotation, child is on top of node and parent
					child.child[0]->balanceFactor = balanceLeftChild;
					child.child[1]->balanceFactor = balanceLeftChild + childSqaure;
					child.balanceFactor = 0; // child is always in balance
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
				int balanceSubtree(const _avlbasenode* const subtreeRoot, _avlbasenode* node, int index, const int insertRemove) throw() {
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
							_avlbasenode& child = *node->child[rotate];
							if(child.balanceFactor == -heightChange) {
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
								assert(child.balanceFactor == 0 || child.balanceFactor == heightChange);
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
						assert(node != NULL);
						index = _getIndex(*node);
						node = node->parent;
					}

					// we reached the root of subtree; hence, our height changed by one
					return 1;
				}

				/*
				 * Removes a given node from the tree. If left subtree is present, node is replaced by largest ancestor of it
				 * to maintain tree order. Otherwise, node is simply removed. Tree re-balancing might occur.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				void removeNode(const _avlbasenode& node) throw() {
					int index = _getIndex(node);
					_avlbasenode* largestAncestor;

					if(node.child[0] != NULL) {
						largestAncestor = node.child[0];
						while(largestAncestor->child[1] != NULL) {
							largestAncestor = largestAncestor->child[1];
						}

						assert(largestAncestor->parent != NULL);
						_avlbasenode& p_ancestor = *largestAncestor->parent;

						// remove largest child from subtree
						int heightDifferenz = 0;
						if(&p_ancestor != &node) { // regular case
							// replace ancestor by its left sub-tree (in order to remove ancestor from tree)
							replaceChildBySubtree(&p_ancestor, 1, largestAncestor->child[0]);

							// check for special case, in which left hand child (of node that is remove) has a single right leaf-child
							// in this case, replaceChildBySubtree(...), decreased subtree height by one
							heightDifferenz = &p_ancestor == node.child[0] && p_ancestor.child[0] == NULL;

							// balance subtree upward to the node that is removed
							heightDifferenz += balanceSubtree(&node, &p_ancestor, 1, 1);
						} else { // ancestor is direct child of node
							// replace ancestor by its left sub-tree
							replaceChildBySubtree(&p_ancestor, 0, largestAncestor->child[0]);
							heightDifferenz = 1;
						}

						// use largest ancestor to replace node to be removed
						replaceChildBySubtree(largestAncestor, 0, node.child[0]);
						replaceChildBySubtree(largestAncestor, 1, node.child[1]);
						replaceChildBySubtree(node.parent, index, largestAncestor);
						largestAncestor->balanceFactor = node.balanceFactor;

						if(heightDifferenz == 0)
							return;

						index = 0; // lower tree is left child (prepare for balanceSubtree(...))
					} else { // node has no left subtree or left subtree is exactly one node
						// replace node by subtree
						replaceChildBySubtree(node.parent, index, node.child[1]);

						// start re-balancing upper tree above node, because node is not present any longer
						largestAncestor = node.parent;
					}

					// balance tree upward to root starting at removed node (ie, its replacement or its parent)
					balanceSubtree(NULL, largestAncestor, index, 1);
				}
			///
			/// \endcond
			///

			public:
				/**
				 * \brief Removes all elements from the tree.
				 *
				 * Complexity: O(n) with n being the current number of values contained in the tree.
				 */
				void clear() throw() {
					if(root != NULL) {
						delete root;
						root = NULL;
						currentSize = 0;
						beforeFirst.next = &afterLast;
						afterLast.prev = &beforeFirst;
					}
				}

				/**
				 * \brief Returns `true` if the tree is empty, ie, does not contain any elements. Otherwise, `false` is returned.
				 *
				 * Complexity: O(1)
				 */
				bool empty() const throw() {
					return !root;
				}

				/**
				 * \brief Returns the current number of elements contained in the tree.
				 *
				 * The count is only correct, if the tree always contained less than `UINT_MAX` elements. If `UINT_MAX` or more elements have been contained in
				 * the tree, size() returns `UINT_MAX` (even if the current number of elements is less than `UINT_MAX`). The count is automatically corrected,
				 * if the tree gets empty. If this case, the count is set to zero. The count can be recomputed using recomputeSize().
				 *
				 * Complexity: O(1)
				 *
				 *  _See limits.h for UNIT_MAX._
				 */
				size_t size() const throw() {
					return currentSize;
				}

				// TODO
				size_t max_size() const throw() {
					return UINT_MAX;
				}

		};

		/**
		 * \brief AVL tree container. An AVL tree (named after its inventors, G.M. Adelson-Velsky and J.M. Landis) is a sorted, balanced, binary tree.
		 *
		 * @ref avltree requires a total order on the value's type __T__ (specified by "<") and cannot store duplicates. By default, `std::less<T>` is used
		 * to insert values at the correct position in the tree. If __T__ is a user-defined type/class, it must provide an implementation of
		 * less-than operator: `bool operator<(const T &) const`
		 *
		 * If pointer types are used, a user-defined comparator __C__ should be provided. Otherwise, values are ordered by their memory addresses.
		 * Furthermore, inserted values must not be modified after inserting. Otherwise, internal tree structure might get invalid. Thus, no
		 * guarantees about tree behavior can be given if values inserted by pointer or reference are modified after insertion.
		 *
		 * A user-defined comparator must provide an implementation of the function call operator that returns true if first parameter is less
		 * than second parameter and false otherwise: `bool operator()(const T, const T) const`
		 *
		 * Additionally, a key type __K__ can be provided (that is equal to value type by default) that enables key-based find and remove operation.
		 * If a key type is used, a user-defined comparator must be specified that provides three function call operators:
		 *   1. `bool operator()(const T, const T) const`
		 *   2. `bool operator()(const K, const T) const`
		 *   3. `bool operator()(const T, const K) const`
		 *
		 * The user-defined comparator must ensure, that all three function call operators return true if the first parameter is less than the
		 * second parameter. Additionally, it must be ensured that for any two used value/key pairs `V1/K1` and `V2/K2` it must hold that
		 * `V1 < V2 <=> K1 < V2 <=> V1 < K2`.
		 */

		// TODO: make STL container conform... see http://www.cplusplus.com/reference/stl/
		// TODO: make C++ 11 or C++14 compatible

		template<class T, class C, class K>
		class avltree : public avltree_base {
			public:
				// C++ Standard: container required typedefs
				typedef T										value_type;
				typedef T&										reference;
				typedef const T&								const_reference;
				typedef _avltree_const_iterator<T,C,K>			iterator;
				typedef iterator								const_iterator;
				typedef typename iterator::difference_type		difference_type;
				typedef size_t									size_type;

				// C++ Standard: associative container required typedefs
				// TODO: resolve conflict of key_type and the currently used key-construction
				typedef T										key_type;
				typedef C										key_compare;
				typedef C										value_compare;
				// what is Compare() ??
				// TODO add constructor with Compare() object as parameter
				// TODO add constructor with avltree(iter.start,iter.stop_exclusive)
				// TODO add constructor with avltree(iter.start,iter.stop_exclusive, Compare())
				// TODO add constructor with avltree(initializer_list<value_type>)

			///
			/// \cond
			///
			protected:
				typedef _avlnode<T>				avlnode;

				C less_than;

				template<class T1, class T2>
				inline bool equals(const T1& v1, const T2& v2) const {
					return !(less_than(v1, v2)
							|| less_than(v2, v1));
				}

				inline avlnode* createNewNode(const T& value, _avlbasenode& before, _avlbasenode& after, avlnode* const parent) const throw(std::bad_alloc) {
					avlnode* newNode = new avlnode(value, before, after, parent);
					if(newNode == NULL) {
						throw std::bad_alloc();
					}
					return newNode;
				}

				/*
				 * Searches for a given value starting at the root. Assumes root is not NULL. Returns founded node or last
				 * visited(!) leaf. Hence, returned node can or cannot contain value---depending if value is stored in tree
				 * or not.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				template<class KT>
				avlnode& findNode(const KT& key) const {
					assert(root != NULL);

					assert(dynamic_cast<avlnode*>(root) != NULL);
					const avlnode* node = static_cast<avlnode*>(root);

					while(true) {
						if(equals(key, node->value)) {
							break;
						}

						if(less_than(key, node->value)) {
							if(node->child[0] == NULL) {
								break;
							} else {
								assert(dynamic_cast<avlnode*>(node->child[0]) != NULL);
								node = static_cast<avlnode*>(node->child[0]);
								continue;
							}
						}

						assert(less_than(node->value, key));
						if(node->child[1] == NULL) {
							break;
						} else {
							assert(dynamic_cast<avlnode*>(node->child[1]) != NULL);
							node = static_cast<avlnode*>(node->child[1]);
							continue;
						}
					}

					return *const_cast<avlnode*>(node);
				}

				/*
				 * Template function to cover search by value and search by key. Searches for a given value starting at the root.
				 * Returns value if present. Otherwise, an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				template<class KT>
				inline T findInternal(const KT& key) const throw(AvltreeException) {
					if(root != NULL) {
						const avlnode& node = findNode(key);

						if(equals(key, node.value)) {
							return node.value;
						}
					}

					throw AvltreeException();
				}

				/*
				 * Removes a given node from the tree, deletes the allocated node memory, and returns the value contained in the node.
				 */
				T removeNodeInternal(avlnode& node) throw() {
					removeNode(node);

					const T value = node.value;
					// set children to NULL -> otherwise, "delete node" recursively deletes children nodes
					node.child[0] = NULL;
					node.child[1] = NULL;
					node.prev->next = node.next;
					node.next->prev = node.prev;
					delete &node;

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
				size_type removeInternal(const KT& value) {
					if(root != NULL) {
						avlnode& node = findNode(value);

						if(equals(value, node.value)) {
							removeNodeInternal(node);
							return 1;
						}
					}

					return 0;
				}
			///
			/// \endcond
			///

			public:
				///
				/// \cond
				/// TODO: remove (only for debugging)
				///
				const _avlbasenode* getRoot() const throw() {
					return root;
				}
				///
				/// \endcond
				///

				/**
				 * \brief Constructs an empty @ref avltree.
				 *
				 * Complexity: O(1)
				 */
				avltree() { /* empty */ }

				// TODO: copy-constructor and assignment-operator should not throw (753)
				/**
				 * \brief Copy-Constructor. Constructs a deep-copy of the given tree.
				 *
				 * In case of memory allocation error an `bad_alloc` exception is thrown.
				 *
				 * Complexity: O(n) with n being the number of values contained in the given tree.
				 */
				avltree(const avltree& tree) throw(std::bad_alloc) {
					// TODO
				}

				/**
				 * \brief Assignment Operator. Assigns a deep-copy of the given @ref avltree.
				 *
				 * In case of memory allocation error an `bad_alloc` exception is thrown.
				 *
				 * Complexity: O(n) with n being the number of values contained in the given tree.
				 */
				avltree& operator=(const avltree& tree) throw(std::bad_alloc) {
					// TODO
					return *this;
				}

				// TODO
				// copy-constructor and assignmnet-operator for rvalue inputs -> O(1)

				// TODO
				bool operator!=(const avltree& tree) const throw() {
					// iterate and stop if unequal elemet is found
					return false;
				}

				// TODO
				bool operator==(const avltree& tree) const throw() {
					return !operator!=(tree);
				}

				// TODO -> must have O(1) -> may not throw -> do not invalidate refs, pointers, or iterators (expect .end())
				void swap(const avltree& tree) throw() {

				}

				/**
				 * \brief Inserts a new value into the tree.
				 *
				 * If value is already present, tree is not altered and a pair <it_found_node,false> is returned. If value is not present, it is inserted
				 * (including possible re-balancing of the tree) and <it_new_node,true> is returned.
				 *
				 * In case of memory allocation error, tree is not altered and an `bad_alloc` exception is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				std::pair<iterator,bool> insert(const T& value) throw(std::bad_alloc) {
					avlnode* newNode;

					if(root != NULL) {
						avlnode& node = findNode(value);

						if(equals(value, node.value)) { // duplicate found; returned leaf contains value
							return std::pair<iterator,bool>(const_iterator(&node),false);
						}

						// we insert below returned leaf
						const int index = !less_than(value, node.value); // value < node->value => index = 0; index = 1, otherwise
						assert(node.child[index] == NULL);

						_avlbasenode* before;
						_avlbasenode* after;
						if(index == 0) { // new node is inserted "before" parent node
							before = node.prev;
							after = &node;
						} else { // new node is inserted "after" parent node
							assert(index == 1);
							before = &node;
							after = node.next;
						}

						assert(before != NULL);
						assert(after != NULL);
						newNode = createNewNode(value, *before, *after, &node);
						node.child[index] = newNode;
						balanceSubtree(NULL, &node, index, 0);
					} else {
						assert(currentSize == 0);

						// else: empty tree; create new root
						newNode = createNewNode(value, beforeFirst, afterLast, NULL);
						root = newNode;
					}

					if(currentSize < UINT_MAX) {
						++currentSize;
					}

					return std::pair<iterator,bool>(const_iterator(newNode),true);
				}

				std::pair<iterator,bool> insert(iterator& it) throw(std::bad_alloc) {
					return insert(*it);
				}
				// TODO: by emplace constructibe from i to j (both iterator
				void insert(iterator i, iterator j) {
				}

				// TODO:
				void insert() { // paramters initializer_list<value_type>

				}

				// TODO
				// O(log n)
				std::pair<iterator,bool> emplace(int args) { // <- fix argument list [std::forward<Args>(args)...]
					return std::pair<iterator,bool>(cend,false);
				}

				// TODO -> we can (and do) ignore p
				// does it make sense, because we do not return a pair???
				iterator emplace_hint(const_iterator& p, int args) { // <- fix argument list [std::forward<Args>(args)...]
					return emplace(args).first();
				}
				/**
				 * \brief Searches for an element in the tree by value.
				 *
				 * Returns a copy of the value if present; otherwise an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				// TODO: remove iterator (const iterator for const avltree <= how to do this?)
				T find(const T& value) const throw(AvltreeException) {
					return findInternal(value);
				}

				/**
				 * \brief Searches for an element in the tree by key.
				 *
				 * Returns a copy of the value if present; otherwise an AvltreeException is thrown.
				 * By default (ie, if no key type template parameter is specified), findByKey() is the same as find().
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				// TODO -> see find
				T findByKey(const K& key) const throw(AvltreeException) {
					return findInternal(key);
				}

				// TODO
				size_type count(const T& value) const throw() {
					return 0;
				}

				// TODO
				size_type countByKey(const K& key) const throw() {
					return 0;
				}

				// TODO: return const iterator for const avltree <= how to do this?
				// upper_bound_byKey
				iterator upper_bound(const T& value) const throw() {
					return iterator();
				}

				// TODO: return const iterator for const avltree <= how to do this?
				// lower_bound_byKey
				iterator lower_bound(const T& value) const throw() {
					return iterator();
				}

				// TODO: return pair<const iterator,const iterator> for const avltree <= how to do this?
				// equal_range_byKey
				std::pair<iterator,iterator> equal_range(const T& value) const throw() {
					// make_pair(a.lower_bound(k),a.upper_bound(k))
					return std::pair<iterator,iterator>(iterator(),iterator());
				}

				/**
				 * \brief Removes an element from the tree.
				 *
				 * Returns a copy of the removed element value if present; otherwise an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				size_type erase(const T& value) throw() {
					return removeInternal(value);
				}

				// TODO
				iterator erase(iterator& it) throw() {
					iterator rit = it++;
					removeNodeInternal(it);
					return rit;
				}

				// TODO
				iterator erase(iterator& i, iterator& j) throw() { // from, to(exclusive)

					return j;
				}

				/**
				 * \brief Removes an element from the tree by given key.
				 *
				 * Returns a copy of the removed element value if present; otherwise an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of values contained in the tree.
				 */
				// TODO: remove exception -> see erase
				T eraseByKey(const K& key) throw(AvltreeException) {
					return removeInternal(key);
				}

				/**
				 * \brief Returns the value of the smallest element stored in the tree.
				 *
				 * If tree in empty, an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of elements contained in the tree.
				 */
				const T& front() const throw(AvltreeException) {
					assert(beforeFirst.next != NULL);
					const _avlbasenode& min = *beforeFirst.next;

					if(&min != &afterLast) {
						assert(dynamic_cast<const avlnode* const>(&min) != NULL);
						return static_cast<const avlnode&>(min).value;
					}

					throw AvltreeException();
				}

				/**
				 * \brief Removes the smallest element stored in the tree and returns its value.
				 *
				 * If tree in empty, an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of elements contained in the tree.
				 */
				// TODO -> should it be pop_front()? -> pop_front may not throw exception
				T pop() throw(AvltreeException) {
					assert(beforeFirst.next != NULL);
					_avlbasenode& min = *beforeFirst.next;

					if(&min != &afterLast) {
						assert(dynamic_cast<avlnode* const>(&min) != NULL);
						return removeNodeInternal(static_cast<avlnode&>(min));
					}

					throw AvltreeException();
				}

				/**
				 * \brief Returns the value of the largest elements stored in the tree.
				 *
				 * If tree in empty, an AvltreeException is thrown.
				 *
				 * Complexity: O(log(n)) with n being the current number of elements contained in the tree.
				 */
				// TODO -> should it be pop_back()? -> pop_back may not throw exception
				const T& back() const throw(AvltreeException) {
					assert(afterLast.prev != NULL);
					const _avlbasenode& max = *afterLast.prev;

					if(&max != &beforeFirst) {
						assert(dynamic_cast<const avlnode* const>(&max) != NULL);
						return static_cast<const avlnode&>(max).value;
					}

					throw AvltreeException();
				}

				/**
				 * \brief Returns a bi-directional read-only (const) iterator that points to the first (smallest) element in the tree.
				 */
				// TODO: verify: semantics should be "const_cast<T const&>(avltree).begin();"
				const_iterator cbegin() const throw() {
					return beforeFirst.next != &afterLast ? const_iterator(beforeFirst.next) : const_iterator(&afterLast);
				}

				/**
				 * \brief Returns a bi-directional read-only (const) iterator that points to the first (smallest) element in the tree.
				 */
				// TODO regular iterator; const iterator in case of "T == const datatype"
				// does this make sense in our case -> we only want to have const iterators anyway
				iterator begin() const throw() {
					return cbegin();
				}

				/**
				 * \brief Returns a bi-directional read-only (const) iterator that points to the position after the last largest) element in the tree.
				 */
				// TODO: verify: semantics should be "const_cast<T const&>(avltree).end();"
				const_iterator cend() const throw() {
					return const_iterator(&afterLast);
				}

				/**
				 * \brief Returns a bi-directional read-only (const) iterator that points to the position after the last largest) element in the tree.
				 */
				iterator end() const throw() {
					return cend();
				}

				// TODO: add reverse iterator functions

				// TODO -> need to return object of given type (how is this done?)
				key_compare key_comp() const throw() {
					return avltree<T>::key_compare;
				}

				// TODO -> need to return object of given type (how is this done?)
				value_compare value_comp() const throw() {
					return avltree<T>::value_compare;
				}
		};

		// TODO -> must have O(1) -> may not throw -> do not invalidate refs, pointers, or iterators (expect .end())
		template<class T>
		void swap(const avltree<T>& tree1, const avltree<T>& tree2) {

		}
	}
}

#endif
