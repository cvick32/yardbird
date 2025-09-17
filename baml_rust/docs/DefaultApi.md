# \DefaultApi

All URIs are relative to *http://localhost:2024*

Method | HTTP request | Description
------------- | ------------- | -------------
[**analyze_counterexample**](DefaultApi.md#analyze_counterexample) | **POST** /call/AnalyzeCounterexample | 
[**propose_invariant**](DefaultApi.md#propose_invariant) | **POST** /call/ProposeInvariant | 
[**suggest_lemmas**](DefaultApi.md#suggest_lemmas) | **POST** /call/SuggestLemmas | 



## analyze_counterexample

> models::InvariantSuggestions analyze_counterexample(analyze_counterexample_request)


### Parameters


Name | Type | Description  | Required | Notes
------------- | ------------- | ------------- | ------------- | -------------
**analyze_counterexample_request** | [**AnalyzeCounterexampleRequest**](AnalyzeCounterexampleRequest.md) |  | [required] |

### Return type

[**models::InvariantSuggestions**](InvariantSuggestions.md)

### Authorization

No authorization required

### HTTP request headers

- **Content-Type**: application/json
- **Accept**: application/json

[[Back to top]](#) [[Back to API list]](../README.md#documentation-for-api-endpoints) [[Back to Model list]](../README.md#documentation-for-models) [[Back to README]](../README.md)


## propose_invariant

> models::InvariantSuggestions propose_invariant(propose_invariant_request)


### Parameters


Name | Type | Description  | Required | Notes
------------- | ------------- | ------------- | ------------- | -------------
**propose_invariant_request** | [**ProposeInvariantRequest**](ProposeInvariantRequest.md) |  | [required] |

### Return type

[**models::InvariantSuggestions**](InvariantSuggestions.md)

### Authorization

No authorization required

### HTTP request headers

- **Content-Type**: application/json
- **Accept**: application/json

[[Back to top]](#) [[Back to API list]](../README.md#documentation-for-api-endpoints) [[Back to Model list]](../README.md#documentation-for-models) [[Back to README]](../README.md)


## suggest_lemmas

> models::InvariantSuggestions suggest_lemmas(suggest_lemmas_request)


### Parameters


Name | Type | Description  | Required | Notes
------------- | ------------- | ------------- | ------------- | -------------
**suggest_lemmas_request** | [**SuggestLemmasRequest**](SuggestLemmasRequest.md) |  | [required] |

### Return type

[**models::InvariantSuggestions**](InvariantSuggestions.md)

### Authorization

No authorization required

### HTTP request headers

- **Content-Type**: application/json
- **Accept**: application/json

[[Back to top]](#) [[Back to API list]](../README.md#documentation-for-api-endpoints) [[Back to Model list]](../README.md#documentation-for-models) [[Back to README]](../README.md)

