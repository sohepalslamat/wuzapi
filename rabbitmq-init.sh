#!/bin/sh
# RabbitMQ initialization script to set up automatic message expiration policies
# This script sets TTL (Time To Live) and max-length policies for queues
# Uses RabbitMQ Management HTTP API for cross-container access

set -e

RABBITMQ_HOST=${RABBITMQ_HOST:-rabbitmq}
RABBITMQ_USER=${RABBITMQ_DEFAULT_USER:-wuzapi}
RABBITMQ_PASS=${RABBITMQ_DEFAULT_PASS:-wuzapi}
RABBITMQ_VHOST=${RABBITMQ_DEFAULT_VHOST:-/}
RABBITMQ_PORT=15672

echo "Waiting for RabbitMQ Management API to be ready..."
MAX_RETRIES=30
RETRY_COUNT=0

while [ $RETRY_COUNT -lt $MAX_RETRIES ]; do
  if curl -s -u "${RABBITMQ_USER}:${RABBITMQ_PASS}" "http://${RABBITMQ_HOST}:${RABBITMQ_PORT}/api/overview" > /dev/null 2>&1; then
    echo "RabbitMQ Management API is ready!"
    break
  fi
  echo "Waiting for RabbitMQ Management API... (attempt $((RETRY_COUNT + 1))/$MAX_RETRIES)"
  sleep 2
  RETRY_COUNT=$((RETRY_COUNT + 1))
done

if [ $RETRY_COUNT -eq $MAX_RETRIES ]; then
  echo "ERROR: RabbitMQ Management API did not become ready in time"
  exit 1
fi

echo "Setting up RabbitMQ policies..."

# URL encode the vhost (replace / with %2F)
VHOST_ENCODED=$(echo "$RABBITMQ_VHOST" | sed 's|/|%2F|g')

# Set queue limits as a SINGLE policy.
#
# RabbitMQ applies only ONE policy per queue -- the highest-priority match.
# Two separate policies sharing pattern ".*" and priority 1 therefore do NOT
# combine: one silently wins and the other never applies. That is exactly what
# happened in production (2026-08-29): message-ttl won, max-length never applied,
# and whatsapp_events grew to 75,793 messages (past its 50,000 cap) until memory
# pressure closed the publisher channel and every publish failed with a 504.
# Keep both definitions in ONE policy so both take effect.
#
# message-ttl: 86400000 ms = 24 hours
# max-length:  50000 messages (oldest dropped when the limit is reached)
echo "Setting queue limits policy (TTL 24h + max-length 50000)..."
curl -s -u "${RABBITMQ_USER}:${RABBITMQ_PASS}" \
  -X PUT \
  -H "Content-Type: application/json" \
  -d '{"pattern":".*","definition":{"message-ttl":86400000,"max-length":50000},"apply-to":"queues","priority":10}' \
  "http://${RABBITMQ_HOST}:${RABBITMQ_PORT}/api/policies/${VHOST_ENCODED}/limits" > /dev/null || echo "Policy may already exist"

# Remove the superseded split policies if an older deployment created them.
for legacy in message-ttl max-length; do
  curl -s -u "${RABBITMQ_USER}:${RABBITMQ_PASS}" \
    -X DELETE \
    "http://${RABBITMQ_HOST}:${RABBITMQ_PORT}/api/policies/${VHOST_ENCODED}/${legacy}" > /dev/null 2>&1 || true
done

echo ""
echo "=========================================="
echo "RabbitMQ policies configured successfully!"
echo "=========================================="
echo "  ✓ Single policy 'limits' (priority 10):"
echo "      - Message TTL: 24 hours (messages older than 24h are auto-deleted)"
echo "      - Max queue length: 50000 messages (oldest dropped when limit reached)"
echo ""
echo "To verify policies, run:"
echo "  docker exec wuzapi-rabbitmq-1 rabbitmqctl list_policies"
echo ""
