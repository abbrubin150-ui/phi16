"""
Moral Triangle Feedback Loop

Implements the closed feedback loop between T10 (Measure), T11 (Monitor), and T12 (Learn).

The Loop:
  T11 (Monitor) identifies state/anomaly
    ↓
  T10 (Measure) quantifies and evaluates
    ↓
  T12 (Learn) extracts insights
    ↓
  T08 (Govern) updates policy
    ↓
  T09 (Standardize) implements new standards
    ↓
  T07 (Automation) updates
    ↓
  Back to T11 (Monitor)

Critical Property: When T10, T11, T12 operate together in 1:1:1 ratio,
they achieve a 2.5× synergy multiplier.
"""

from typing import Dict, Any, Optional, List
from datetime import datetime
from .registry import TokenRegistry
from .base import TokenState


class MoralTriangle:
    """
    Manages the Moral Triangle feedback loop.

    Coordinates T10 (Measure), T11 (Monitor), and T12 (Learn) to create
    a continuous improvement cycle.
    """

    def __init__(self, registry: TokenRegistry):
        self.registry = registry
        self._cycle_history: List[Dict[str, Any]] = []
        self._synergy_active = False

    def check_synergy_conditions(self) -> tuple[bool, Optional[str]]:
        """
        Check if conditions are met for 2.5× synergy.

        Conditions:
        1. All three tokens (T10, T11, T12) are ACTIVE
        2. They are operating in approximately 1:1:1 ratio

        Returns:
            (synergy_active, reason_if_not)
        """
        t10 = self.registry.get_token("T10")
        t11 = self.registry.get_token("T11")
        t12 = self.registry.get_token("T12")

        # Check all exist
        if not all([t10, t11, t12]):
            return False, "Not all moral triangle tokens found"

        # Check all active
        if not all([
            t10.state == TokenState.ACTIVE,
            t11.state == TokenState.ACTIVE,
            t12.state == TokenState.ACTIVE
        ]):
            inactive = []
            if t10.state != TokenState.ACTIVE:
                inactive.append("T10")
            if t11.state != TokenState.ACTIVE:
                inactive.append("T11")
            if t12.state != TokenState.ACTIVE:
                inactive.append("T12")
            return False, f"Tokens not active: {', '.join(inactive)}"

        # Check 1:1:1 ratio (based on activation counts)
        activations = [
            t10.metrics.activations,
            t11.metrics.activations,
            t12.metrics.activations
        ]

        if min(activations) == 0:
            return False, "Not all tokens have been activated"

        # Calculate ratio variance
        avg = sum(activations) / len(activations)
        variance = sum((x - avg) ** 2 for x in activations) / len(activations)
        stddev = variance ** 0.5

        # Allow up to 20% deviation from perfect 1:1:1
        if stddev / avg > 0.2:
            return False, f"Ratio not 1:1:1 (stddev/avg = {stddev/avg:.2f})"

        return True, None

    def calculate_synergy_multiplier(self) -> float:
        """
        Calculate the current synergy multiplier.

        Returns:
            Multiplier value (1.0 to 2.5)
        """
        synergy_active, _ = self.check_synergy_conditions()

        if synergy_active:
            return 2.5
        else:
            # Partial synergy based on how many tokens are active
            t10 = self.registry.get_token("T10")
            t11 = self.registry.get_token("T11")
            t12 = self.registry.get_token("T12")

            active_count = sum([
                1 if t10 and t10.state == TokenState.ACTIVE else 0,
                1 if t11 and t11.state == TokenState.ACTIVE else 0,
                1 if t12 and t12.state == TokenState.ACTIVE else 0
            ])

            # Linear scaling: 1.0 + (active/3) * 1.5
            return 1.0 + (active_count / 3) * 1.5

    def execute_cycle(
        self,
        monitored_event: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        Execute one complete cycle of the moral triangle.

        Args:
            monitored_event: Event detected by T11 (Monitor)

        Returns:
            Cycle results including insights and recommendations
        """
        cycle_start = datetime.now()
        results = {
            'cycle_id': len(self._cycle_history),
            'start_time': cycle_start,
            'monitored_event': monitored_event,
            'steps': []
        }

        # Step 1: Monitor identifies anomaly
        t11 = self.registry.get_token("T11")
        if t11:
            from .layer3_moral import MonitorToken
            if isinstance(t11, MonitorToken):
                anomaly = t11.monitor_state(
                    state_name=monitored_event.get('state_name', 'unknown'),
                    current_value=monitored_event.get('value'),
                    expected_range=monitored_event.get('expected_range')
                )
                results['steps'].append({
                    'step': 'monitor',
                    'token': 'T11',
                    'anomaly': anomaly
                })

        # Step 2: Measure quantifies
        t10 = self.registry.get_token("T10")
        if t10 and monitored_event.get('value') is not None:
            from .layer3_moral import MeasureToken
            if isinstance(t10, MeasureToken):
                metric_name = monitored_event.get('state_name', 'unknown_metric')
                t10.measure(
                    metric_name=metric_name,
                    value=monitored_event.get('value'),
                    context=monitored_event
                )
                results['steps'].append({
                    'step': 'measure',
                    'token': 'T10',
                    'metric': metric_name
                })

        # Step 3: Learn extracts insights
        t12 = self.registry.get_token("T12")
        insight = None
        if t12 and results['steps']:
            from .layer3_moral import LearnToken
            if isinstance(t12, LearnToken):
                # Extract insight from the cycle
                insight_desc = f"Pattern detected in {monitored_event.get('state_name')}"
                t12.extract_insight(
                    source="moral_triangle_cycle",
                    insight_type="anomaly_pattern",
                    description=insight_desc,
                    supporting_data=monitored_event
                )
                results['steps'].append({
                    'step': 'learn',
                    'token': 'T12',
                    'insight': insight_desc
                })

        # Step 4: Recommend policy update (feeds to T08)
        if t12 and insight:
            from .layer3_moral import LearnToken
            if isinstance(t12, LearnToken):
                t12.recommend_policy_update(
                    target_token="T08",
                    recommendation=f"Update policy based on {monitored_event.get('state_name')}",
                    rationale="Anomaly pattern detected in moral triangle cycle"
                )
                results['steps'].append({
                    'step': 'recommend',
                    'target': 'T08',
                    'recommendation': 'policy_update'
                })

        # Calculate synergy
        multiplier = self.calculate_synergy_multiplier()
        results['synergy_multiplier'] = multiplier
        results['synergy_active'] = multiplier >= 2.5

        # Complete cycle
        results['end_time'] = datetime.now()
        results['duration_ms'] = (results['end_time'] - cycle_start).total_seconds() * 1000

        self._cycle_history.append(results)
        return results

    def get_cycle_statistics(self) -> Dict[str, Any]:
        """Get statistics about moral triangle cycles"""
        if not self._cycle_history:
            return {
                'total_cycles': 0,
                'avg_synergy_multiplier': 0.0,
                'synergy_active_percent': 0.0
            }

        total_cycles = len(self._cycle_history)
        avg_multiplier = sum(c['synergy_multiplier'] for c in self._cycle_history) / total_cycles
        synergy_active_count = sum(1 for c in self._cycle_history if c['synergy_active'])

        return {
            'total_cycles': total_cycles,
            'avg_synergy_multiplier': avg_multiplier,
            'synergy_active_percent': (synergy_active_count / total_cycles) * 100,
            'recent_cycles': self._cycle_history[-5:]  # Last 5 cycles
        }

    def get_triangle_health(self) -> Dict[str, Any]:
        """
        Get health status of the moral triangle.

        Returns comprehensive health metrics.
        """
        t10 = self.registry.get_token("T10")
        t11 = self.registry.get_token("T11")
        t12 = self.registry.get_token("T12")

        synergy_active, synergy_reason = self.check_synergy_conditions()
        multiplier = self.calculate_synergy_multiplier()

        return {
            't10_status': t10.state.value if t10 else 'missing',
            't11_status': t11.state.value if t11 else 'missing',
            't12_status': t12.state.value if t12 else 'missing',
            'synergy_active': synergy_active,
            'synergy_reason': synergy_reason,
            'synergy_multiplier': multiplier,
            'cycle_count': len(self._cycle_history),
            'token_activations': {
                'T10': t10.metrics.activations if t10 else 0,
                'T11': t11.metrics.activations if t11 else 0,
                'T12': t12.metrics.activations if t12 else 0
            }
        }
