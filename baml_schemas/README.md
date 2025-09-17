# BAML Integration for Yardbird

This directory contains BAML (Boundary AI Markup Language) schemas and functions for AI-assisted verification in Yardbird.

## Setup

1. **Install dependencies:**
   ```bash
   npm install
   ```

2. **Generate the BAML client:**
   ```bash
   npm run baml-generate
   ```

3. **Set up OpenAI API key (required for BAML functions):**
   ```bash
   export OPENAI_API_KEY="your-api-key-here"
   ```

## Running the BAML Server

Start the BAML server to handle verification requests:

```bash
npx baml-cli serve
```

The server will run on `http://localhost:2024` by default.

## Testing the Integration

From the main yardbird directory, run the example:

```bash
cargo run --bin baml_example
```

This will:
1. Connect to the BAML server
2. Send a sample verification request based on `array_copy.vmt`
3. Display AI-generated invariant suggestions

## API Endpoints

The BAML server exposes three main endpoints:

- `POST /call/ProposeInvariant` - Generate invariant candidates
- `POST /call/AnalyzeCounterexample` - Analyze failed verification attempts
- `POST /call/SuggestLemmas` - Suggest auxiliary lemmas

## Example Usage in Rust

```rust
use yardbird::baml_client::{BamlClient, VerificationRequest, AnalysisType};

let client = BamlClient::new(None); // Uses default localhost:2024
let suggestions = client.propose_invariant(request).await?;

for candidate in suggestions.candidates {
    println!("Invariant: {}", candidate.formula);
    println!("Confidence: {}%", candidate.confidence);
}
```

## Files

- `baml_src/schemas.baml` - Type definitions for verification context and responses
- `baml_src/invariant_functions.baml` - BAML functions for different analysis types
- `baml_src/clients.baml` - Client and generator configurations
- `generated/baml_client/openapi.yaml` - Generated OpenAPI specification

## Integration with Yardbird

The Rust integration is located in `src/baml_client.rs` and provides:

- Rust types matching the BAML schemas
- HTTP client for calling BAML functions
- Helper functions for extracting verification context from VMT files
- Example binary demonstrating the integration

## Customizing Prompts

Edit the prompt templates in `baml_src/invariant_functions.baml` to:
- Add domain-specific knowledge
- Adjust the output format
- Include additional context or constraints
- Modify the reasoning approach

After changes, regenerate the client with `npm run baml-generate`.