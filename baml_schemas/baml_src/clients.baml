// BAML client configurations
client<llm> GPT4 {
  provider openai
  options {
    model "gpt-4o-mini"
    temperature 0.1
    max_tokens 2000
  }
}

// Alternative client for faster/cheaper operations
client<llm> GPT35 {
  provider openai
  options {
    model "gpt-4o-mini"
    temperature 0.1
    max_tokens 1500
  }
}

// Generator for OpenAPI/REST interface
generator target {
  output_type "rest/openapi"
  output_dir "../generated"
  version "0.1.0"
}