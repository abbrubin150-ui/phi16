"""
Layer 5: Execution (Technical Operations)

Contains tokens for actual technical execution:
- T07 (Automation / אוטומציה) - Priority 86
- T03 (Compute / חישוב) - Priority 85
- T04 (Storage / אחסון) - Priority 85

These tokens perform the actual work, but are constrained by higher layers.
"""

from typing import Optional, Dict, Any, List
from datetime import datetime
from .base import Token, TokenLayer, TokenState


class AutomationToken(Token):
    """
    T07 - Automation (אוטומציה)

    Independent, routine operation without direct human intervention.

    CRITICAL CONSTRAINT: No automation without monitoring (T11)
    Suspended when T15 is active.

    Maps to: B1 Actuator
    """

    def __init__(self):
        super().__init__(
            token_id="T07",
            name_en="Automation",
            name_he="אוטומציה",
            priority=86,
            layer=TokenLayer.EXECUTION,
            description="Independent automated operations"
        )

        # T07 requires T03 (Compute) - no automation without computational power
        self.add_absolute_dependency("T03")

        # T07 requires T11 (Monitor) - "No automation without monitoring"
        self.add_ethical_constraint("T11", "No automation without monitoring")

        # T07 is controlled by T15 (Seriousness)
        self.add_controlled_by("T15")

        # Φ-OS mappings
        self.phi_os_mappings.add("B1 Actuator")

        # Automation-specific state
        self._automated_tasks: Dict[str, Dict[str, Any]] = {}
        self._execution_history: List[Dict[str, Any]] = []

    def register_automated_task(
        self,
        task_id: str,
        task_type: str,
        execution_function: Optional[Any] = None,
        monitoring_required: bool = True
    ) -> None:
        """
        Register an automated task.

        Args:
            task_id: Unique task identifier
            task_type: Type of task
            execution_function: Function to execute
            monitoring_required: Whether monitoring is required (default True)
        """
        self._automated_tasks[task_id] = {
            'type': task_type,
            'execution_function': execution_function,
            'monitoring_required': monitoring_required,
            'registered_at': datetime.now(),
            'execution_count': 0,
            'last_execution': None
        }

    def can_execute_task(
        self,
        task_id: str,
        registry: 'TokenRegistry'
    ) -> tuple[bool, Optional[str]]:
        """
        Check if a task can be executed.

        Enforces the critical constraint: No automation without monitoring.

        Returns:
            (can_execute, reason_if_not)
        """
        if task_id not in self._automated_tasks:
            return False, f"Task {task_id} not registered"

        task = self._automated_tasks[task_id]

        # Check if monitoring is active (T11)
        if task['monitoring_required']:
            t11 = registry.get_token("T11")
            if not t11 or t11.state != TokenState.ACTIVE:
                return False, "Cannot automate without active monitoring (T11)"

        # Check if compute is available (T03)
        t03 = registry.get_token("T03")
        if not t03 or t03.state not in [TokenState.ACTIVE, TokenState.DEGRADED]:
            return False, "Cannot automate without available compute (T03)"

        # Check if suspended by T15
        if self.state == TokenState.SUSPENDED:
            return False, f"Automation suspended: {self._suspension_reason}"

        return True, None

    def execute_task(
        self,
        task_id: str,
        context: Optional[Dict[str, Any]] = None
    ) -> tuple[bool, Optional[str]]:
        """
        Execute an automated task.

        Returns:
            (success, result_or_error)
        """
        if task_id not in self._automated_tasks:
            return False, f"Task {task_id} not found"

        task = self._automated_tasks[task_id]

        # Record execution
        execution_record = {
            'timestamp': datetime.now(),
            'task_id': task_id,
            'context': context or {},
            'success': True,
            'result': None
        }

        # Update task metrics
        task['execution_count'] += 1
        task['last_execution'] = datetime.now()

        self._execution_history.append(execution_record)

        return True, "Task executed"

    def get_task_status(self, task_id: str) -> Optional[Dict[str, Any]]:
        """Get status of an automated task"""
        return self._automated_tasks.get(task_id)


class ComputeToken(Token):
    """
    T03 - Compute (חישוב)

    Available computational power for real-time data processing.

    Limited by T15 and T06 - no computation without security.

    Maps to: QTPU-Φ + PPCD Engines
    """

    def __init__(self):
        super().__init__(
            token_id="T03",
            name_en="Compute",
            name_he="חישוב",
            priority=85,
            layer=TokenLayer.EXECUTION,
            description="Computational power for data processing"
        )

        # T03 requires T06 (Security) - "No computation without security"
        self.add_ethical_constraint("T06", "No computation without security")

        # T03 is controlled by T15 (Seriousness)
        self.add_controlled_by("T15")

        # Φ-OS mappings
        self.phi_os_mappings.add("QTPU-Φ")
        self.phi_os_mappings.add("PPCD Engines")

        # Compute-specific state
        self._compute_budget: float = 100.0  # Percentage available
        self._compute_usage: List[Dict[str, Any]] = []

    def allocate_compute(
        self,
        amount: float,
        purpose: str,
        identity_id: str
    ) -> tuple[bool, Optional[str]]:
        """
        Allocate compute resources.

        Args:
            amount: Amount to allocate (0-100)
            purpose: What this compute is for
            identity_id: Who is requesting it

        Returns:
            (success, error_if_failed)
        """
        if amount > self._compute_budget:
            return False, f"Insufficient compute: requested {amount}, available {self._compute_budget}"

        # If degraded by T15, limit allocation
        if self.state == TokenState.DEGRADED:
            max_allowed = 20.0  # Only 20% when degraded
            if amount > max_allowed:
                return False, f"Compute limited by T15: max {max_allowed}, requested {amount}"

        self._compute_budget -= amount
        self._compute_usage.append({
            'timestamp': datetime.now(),
            'amount': amount,
            'purpose': purpose,
            'identity_id': identity_id,
            'state': self.state.value
        })

        return True, None

    def release_compute(self, amount: float) -> None:
        """Release allocated compute back to the pool"""
        self._compute_budget = min(100.0, self._compute_budget + amount)

    def get_available_compute(self) -> float:
        """Get currently available compute"""
        return self._compute_budget


class StorageToken(Token):
    """
    T04 - Storage (אחסון)

    Preservation of information traces over time.

    Maps to: Ledger + DIA Monotonicity
    """

    def __init__(self):
        super().__init__(
            token_id="T04",
            name_en="Storage",
            name_he="אחסון",
            priority=85,
            layer=TokenLayer.EXECUTION,
            description="Preservation of information over time"
        )

        # T04 requires T13 (Rights) - "No storage of violations"
        self.add_ethical_constraint("T13", "No storage of rights violations")

        # Φ-OS mappings
        self.phi_os_mappings.add("Append-Only Ledger")
        self.phi_os_mappings.add("DIA Monotonicity")

        # Storage-specific state
        self._storage_capacity: float = 1000.0  # GB (example)
        self._storage_used: float = 0.0
        self._stored_items: List[Dict[str, Any]] = []

    def store(
        self,
        item_id: str,
        data_size: float,
        data_type: str,
        identity_id: str,
        metadata: Optional[Dict[str, Any]] = None
    ) -> tuple[bool, Optional[str]]:
        """
        Store data.

        Args:
            item_id: Unique identifier for stored item
            data_size: Size in GB
            data_type: Type of data
            identity_id: Who is storing this
            metadata: Additional metadata

        Returns:
            (success, error_if_failed)
        """
        if self._storage_used + data_size > self._storage_capacity:
            return False, f"Insufficient storage: {data_size}GB needed, {self._storage_capacity - self._storage_used}GB available"

        # Check for rights violations in metadata
        if metadata and metadata.get('contains_rights_violation'):
            return False, "Cannot store data containing rights violations (T13)"

        self._storage_used += data_size
        self._stored_items.append({
            'timestamp': datetime.now(),
            'item_id': item_id,
            'size': data_size,
            'type': data_type,
            'identity_id': identity_id,
            'metadata': metadata or {}
        })

        return True, None

    def retrieve(
        self,
        item_id: str,
        identity_id: str
    ) -> tuple[bool, Optional[Dict[str, Any]]]:
        """
        Retrieve stored data.

        Args:
            item_id: What to retrieve
            identity_id: Who is requesting it

        Returns:
            (success, item_or_error)
        """
        for item in self._stored_items:
            if item['item_id'] == item_id:
                # Simple access control - would integrate with T01 (Data) in real system
                return True, item

        return False, None

    def get_storage_status(self) -> Dict[str, Any]:
        """Get storage status"""
        return {
            'capacity_gb': self._storage_capacity,
            'used_gb': self._storage_used,
            'available_gb': self._storage_capacity - self._storage_used,
            'utilization_percent': (self._storage_used / self._storage_capacity) * 100,
            'total_items': len(self._stored_items)
        }
