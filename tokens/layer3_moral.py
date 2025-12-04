"""
Layer 3: Moral Control (The "Moral Triangle")

Contains three tokens that form a closed feedback loop:
- T10 (Measure / מדידה) - Priority 93
- T11 (Monitor / ניטור) - Priority 89
- T12 (Learn / למידה) - Priority 91

Critical: T10 ↔ T11 ↔ T12 form a closed feedback loop with 2.5× multiplier
when operating together in 1:1:1 ratio.

The loop: Monitor identifies → Measure quantifies → Learn extracts insights →
         Govern updates policy → Standardize implements → Automation updates → back to Monitor
"""

from typing import Optional, Dict, Any, List, Callable
from datetime import datetime
from .base import Token, TokenLayer, TokenState


class MeasureToken(Token):
    """
    T10 - Measure (מדידה)

    "Measurement as a moral act" - what we measure defines what we value.

    Maps to: DIA Metrics + SSM (Semantic State Machine)
    """

    def __init__(self):
        super().__init__(
            token_id="T10",
            name_en="Measure",
            name_he="מדידה",
            priority=93,
            layer=TokenLayer.MORAL_CONTROL,
            description="Measurement as a moral act - defines what we value"
        )

        # Φ-OS mappings
        self.phi_os_mappings.add("DIA Metrics")
        self.phi_os_mappings.add("SSM")

        # Measure-specific state
        self._metrics: Dict[str, Dict[str, Any]] = {}
        self._measurement_history: List[Dict[str, Any]] = []

    def define_metric(
        self,
        metric_name: str,
        metric_type: str,
        measurement_function: Optional[Callable] = None,
        ethical_value: Optional[str] = None
    ) -> None:
        """
        Define a metric to be measured.

        Args:
            metric_name: Name of the metric
            metric_type: Type (e.g., "count", "duration", "ratio", "boolean")
            measurement_function: Function that computes this metric
            ethical_value: Which ethical value this metric represents
        """
        self._metrics[metric_name] = {
            'type': metric_type,
            'measurement_function': measurement_function,
            'ethical_value': ethical_value,
            'defined_at': datetime.now(),
            'measurements': []
        }

    def measure(
        self,
        metric_name: str,
        value: Any,
        context: Optional[Dict[str, Any]] = None
    ) -> None:
        """
        Record a measurement.

        Args:
            metric_name: Which metric to measure
            value: The measured value
            context: Additional context about the measurement
        """
        if metric_name not in self._metrics:
            raise ValueError(f"Metric {metric_name} not defined")

        measurement = {
            'timestamp': datetime.now(),
            'value': value,
            'context': context or {}
        }

        self._metrics[metric_name]['measurements'].append(measurement)
        self._measurement_history.append({
            'metric_name': metric_name,
            **measurement
        })

    def get_metric_value(
        self,
        metric_name: str,
        aggregation: str = "latest"
    ) -> Any:
        """
        Get metric value.

        Args:
            metric_name: Which metric
            aggregation: How to aggregate ("latest", "sum", "avg", "count")
        """
        if metric_name not in self._metrics:
            return None

        measurements = self._metrics[metric_name]['measurements']
        if not measurements:
            return None

        if aggregation == "latest":
            return measurements[-1]['value']
        elif aggregation == "sum":
            return sum(m['value'] for m in measurements if isinstance(m['value'], (int, float)))
        elif aggregation == "avg":
            values = [m['value'] for m in measurements if isinstance(m['value'], (int, float))]
            return sum(values) / len(values) if values else None
        elif aggregation == "count":
            return len(measurements)
        else:
            return measurements[-1]['value']

    def get_all_metrics(self) -> Dict[str, Any]:
        """Get summary of all metrics"""
        return {
            name: {
                'type': info['type'],
                'ethical_value': info['ethical_value'],
                'measurement_count': len(info['measurements']),
                'latest_value': info['measurements'][-1]['value'] if info['measurements'] else None
            }
            for name, info in self._metrics.items()
        }


class MonitorToken(Token):
    """
    T11 - Monitor (ניטור)

    Continuous, unceasing observation of system states.

    Maps to: B2 Safety Monitor + PPCD
    """

    def __init__(self):
        super().__init__(
            token_id="T11",
            name_en="Monitor",
            name_he="ניטור",
            priority=89,
            layer=TokenLayer.MORAL_CONTROL,
            description="Continuous observation of system states"
        )

        # T11 requires T05 (Identity) - no monitoring without identity
        self.add_absolute_dependency("T05")

        # Φ-OS mappings
        self.phi_os_mappings.add("B2 Safety Monitor")
        self.phi_os_mappings.add("PPCD")

        # Monitor-specific state
        self._monitored_states: Dict[str, Dict[str, Any]] = {}
        self._anomalies: List[Dict[str, Any]] = []
        self._alerts: List[Dict[str, Any]] = []

    def monitor_state(
        self,
        state_name: str,
        current_value: Any,
        expected_range: Optional[tuple] = None,
        identity_id: Optional[str] = None
    ) -> Optional[str]:
        """
        Monitor a system state and detect anomalies.

        Args:
            state_name: What is being monitored
            current_value: Current value
            expected_range: Expected range (min, max) if applicable
            identity_id: Who is performing this monitoring

        Returns:
            Anomaly description if detected, None otherwise
        """
        # Record state
        if state_name not in self._monitored_states:
            self._monitored_states[state_name] = {
                'values': [],
                'expected_range': expected_range
            }

        state_record = {
            'timestamp': datetime.now(),
            'value': current_value,
            'identity_id': identity_id
        }
        self._monitored_states[state_name]['values'].append(state_record)

        # Check for anomalies
        anomaly = None
        if expected_range:
            min_val, max_val = expected_range
            if not (min_val <= current_value <= max_val):
                anomaly = f"State {state_name} = {current_value} outside expected range [{min_val}, {max_val}]"

        if anomaly:
            self._anomalies.append({
                'timestamp': datetime.now(),
                'state_name': state_name,
                'current_value': current_value,
                'expected_range': expected_range,
                'description': anomaly
            })

        return anomaly

    def create_alert(
        self,
        alert_type: str,
        severity: str,
        description: str,
        context: Optional[Dict[str, Any]] = None
    ) -> None:
        """
        Create a monitoring alert.

        Args:
            alert_type: Type of alert (e.g., "anomaly", "violation", "performance")
            severity: Severity level (e.g., "low", "medium", "high", "critical")
            description: What happened
            context: Additional context
        """
        alert = {
            'timestamp': datetime.now(),
            'type': alert_type,
            'severity': severity,
            'description': description,
            'context': context or {}
        }
        self._alerts.append(alert)

    def get_recent_anomalies(self, limit: int = 10) -> List[Dict[str, Any]]:
        """Get recent anomalies"""
        return self._anomalies[-limit:][::-1]

    def get_recent_alerts(self, limit: int = 10) -> List[Dict[str, Any]]:
        """Get recent alerts"""
        return self._alerts[-limit:][::-1]


class LearnToken(Token):
    """
    T12 - Learn (למידה)

    Learning from experience to improve continuously.
    "Connects past to future, translates mistakes into renewed protocols"

    Maps to: PPCD/QTPU-Φ Pipeline
    """

    def __init__(self):
        super().__init__(
            token_id="T12",
            name_en="Learn",
            name_he="למידה",
            priority=91,
            layer=TokenLayer.MORAL_CONTROL,
            description="Learning from experience for continuous improvement"
        )

        # T12 requires T04 (Storage) - "No memory = no learning"
        self.add_absolute_dependency("T04")

        # Φ-OS mappings
        self.phi_os_mappings.add("PPCD Pipeline")
        self.phi_os_mappings.add("QTPU-Φ")

        # Learn-specific state
        self._learning_insights: List[Dict[str, Any]] = []
        self._policy_recommendations: List[Dict[str, Any]] = []

    def extract_insight(
        self,
        source: str,
        insight_type: str,
        description: str,
        supporting_data: Optional[Dict[str, Any]] = None
    ) -> None:
        """
        Extract a learning insight from observations.

        Args:
            source: Where this insight came from (e.g., "T11_anomaly", "T10_metric")
            insight_type: Type of insight (e.g., "pattern", "correlation", "failure_mode")
            description: What was learned
            supporting_data: Data supporting this insight
        """
        insight = {
            'timestamp': datetime.now(),
            'source': source,
            'type': insight_type,
            'description': description,
            'supporting_data': supporting_data or {}
        }
        self._learning_insights.append(insight)

    def recommend_policy_update(
        self,
        target_token: str,
        recommendation: str,
        rationale: str,
        based_on_insights: Optional[List[int]] = None
    ) -> None:
        """
        Recommend a policy update based on learning.

        This feeds into T08 (Govern) for "learning governance".

        Args:
            target_token: Which token should update (e.g., "T08", "T09")
            recommendation: What should change
            rationale: Why this change is recommended
            based_on_insights: Indices of insights that support this
        """
        policy_rec = {
            'timestamp': datetime.now(),
            'target_token': target_token,
            'recommendation': recommendation,
            'rationale': rationale,
            'based_on_insights': based_on_insights or [],
            'status': 'pending'
        }
        self._policy_recommendations.append(policy_rec)

    def get_insights(
        self,
        insight_type: Optional[str] = None,
        limit: Optional[int] = None
    ) -> List[Dict[str, Any]]:
        """Get learning insights"""
        insights = self._learning_insights[::-1]  # Most recent first

        if insight_type:
            insights = [i for i in insights if i['type'] == insight_type]

        if limit:
            return insights[:limit]
        return insights

    def get_policy_recommendations(
        self,
        target_token: Optional[str] = None,
        status: Optional[str] = None
    ) -> List[Dict[str, Any]]:
        """Get policy recommendations"""
        recs = self._policy_recommendations[::-1]

        if target_token:
            recs = [r for r in recs if r['target_token'] == target_token]

        if status:
            recs = [r for r in recs if r['status'] == status]

        return recs

    def mark_recommendation_applied(self, recommendation_index: int) -> None:
        """Mark a recommendation as applied"""
        if 0 <= recommendation_index < len(self._policy_recommendations):
            self._policy_recommendations[recommendation_index]['status'] = 'applied'
            self._policy_recommendations[recommendation_index]['applied_at'] = datetime.now()
